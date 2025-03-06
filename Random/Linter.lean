import Lean.Util.SearchPath
import Batteries.Tactic.Lint
import Batteries.Data.Array.Basic
import Lake.CLI.Main

open Lean Core Elab Command Batteries.Tactic.Lint
open System (FilePath)

open Lake

/-- Returns the root modules of `lean_exe` or `lean_lib` default targets in the Lake workspace. -/
def resolveDefaultRootModules : IO (Array Name) := do
  -- load the Lake workspace
  let (elanInstall?, leanInstall?, lakeInstall?) ← findInstall?
  let config ← MonadError.runEIO <| mkLoadConfig { elanInstall?, leanInstall?, lakeInstall? }
  let some workspace ← loadWorkspace config |>.toBaseIO
    | throw <| IO.userError "failed to load Lake workspace"

  -- resolve the default build specs from the Lake workspace (based on `lake build`)
  let defaultBuildSpecs ← match resolveDefaultPackageTarget workspace workspace.root with
    | Except.error e => IO.eprintln s!"Error getting default package target: {e}" *> IO.Process.exit 1
    | Except.ok targets => pure targets

  -- build an array of all root modules of `lean_exe` and `lean_lib` build targets
  let defaultTargetModules := defaultBuildSpecs.flatMap <|
    fun target => match target.info with
      | BuildInfo.libraryFacet lib _ => lib.roots
      | BuildInfo.leanExe exe => #[exe.config.root]
      | _ => #[]
  return defaultTargetModules

/--
Return an array of the modules to lint.

If `specifiedModule` is not `none` return an array containing only `specifiedModule`.
Otherwise, resolve the default root modules from the Lake workspace. -/
def determineModulesToLint : IO (Array Name) := do
    println!"Automatically detecting modules to lint"
    let defaultModules ← resolveDefaultRootModules
    println!"Default modules: {defaultModules}"
    return defaultModules

/-- Run the Batteries linter on a given module and update the linter if `update` is `true`. -/
unsafe def runLinterOnModule (module : Name): IO Unit := do
  initSearchPath (← findSysroot)
  -- If the linter is being run on a target that doesn't import `Batteries.Tactic.List`,
  -- the linters are ineffective. So we import it here.
  let lintModule := `Batteries.Tactic.Lint
  let child ← IO.Process.spawn {
    cmd := (← IO.getEnv "LAKE").getD "lake"
    args := #["build", s!"+{lintModule}"]
    stdin := .null
  }
  _ ← child.wait
  let child ← IO.Process.spawn {
    cmd := (← IO.getEnv "LAKE").getD "lake"
    args := #["build", s!"+{module}" , "--log-level=error"]
    stdin := .null
  }
  _ ← child.wait
  let nolints ← pure #[]
  unsafe Lean.enableInitializersExecution
  let env ← importModules #[module, lintModule] {} (trustLevel := 1024)
  Prod.fst <$> (CoreM.toIO · { fileName := "", fileMap := default } { env }) do
    let decls ← getDeclsInPackage module.getRoot
    let linters ← getChecks (slow := true) (runAlways := none) (runOnly := [
      "simpVarHead".toName,
      -- "docBlame".toName,
      "simpComm".toName,
      "defLemma".toName,
      "simpNF".toName,
      "unusedHavesSuffices".toName,
      "deprecatedNoSince".toName,
      "unusedArguments".toName,
      "nonClassInstance".toName,
      "structureInType".toName,
      "checkType".toName,
      "checkUnivs".toName,
      "dupNamespace".toName,
      "synTaut".toName,
      "impossibleInstance".toName
    ])
    let results ← lintCore decls linters
    let results := results.map fun (linter, decls) =>
      .mk linter <| nolints.foldl (init := decls) fun decls (linter', decl') =>
        if linter.name == linter' then decls.erase decl' else decls
    let failed := results.any (!·.2.isEmpty)
    if failed then
      let fmtResults ←
        formatLinterResults results decls (groupByFilename := true) (useErrorFormat := true)
          s!"in {module}" (runSlowLinters := true) .medium linters.size
      IO.print (← fmtResults.toString)
      IO.Process.exit 1
    else
      IO.println s!"-- Linting passed for {module}."

unsafe def main : IO Unit := do
  let modulesToLint ← determineModulesToLint
  modulesToLint.forM <| runLinterOnModule
