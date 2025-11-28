import Lean.Util.Path
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

  -- build an array of all root modules of `lean_exe` and `lean_lib` default targets
  let defaultTargetModules := workspace.root.defaultTargets.flatMap fun target =>
    if let some lib := workspace.root.findLeanLib? target then
      lib.roots
    else if let some exe := workspace.root.findLeanExe? target then
      #[exe.config.root]
    else
      #[]
  return defaultTargetModules

/--
Return an array of the modules to lint.

If `specifiedModule` is not `none` return an array containing only `specifiedModule`.
Otherwise, resolve the default root modules from the Lake workspace. -/
def determineModulesToLint  : IO (Array Name) := do
  println!"Automatically detecting modules to lint"
  let defaultModules ← resolveDefaultRootModules
  println!"Default modules: {defaultModules}"
  return defaultModules

unsafe def runLinterOnModule (module : Name): IO Unit := do
  initSearchPath (← findSysroot)
    -- run `lake build module`
  let child ← IO.Process.spawn {
    cmd := (← IO.getEnv "LAKE").getD "lake"
    args := #["build", s!"+{module}", "-q"]
    stdin := .null
  }
  _ ← child.wait
  -- If the linter is being run on a target that doesn't import `Batteries.Tactic.List`,
  -- the linters are ineffective. So we import it here.
  let lintModule := `Batteries.Tactic.Lint
  let lintFile ← findOLean lintModule
  unless (← lintFile.pathExists) do
    let child ← IO.Process.spawn {
      cmd := (← IO.getEnv "LAKE").getD "lake"
      args := #["build", s!"+{lintModule}"]
      stdin := .null
    }
    _ ← child.wait
  let nolints ← pure #[]
  unsafe Lean.enableInitializersExecution
  let env ← importModules #[module, lintModule] {} (trustLevel := 1024) (loadExts := true)
  let ctx := { fileName := "", fileMap := default }
  let state := { env }
  Prod.fst <$> (CoreM.toIO · ctx state) do
    let decls ← getDeclsInPackage module.getRoot
    let linters ← getChecks (slow := true) (runAlways := none) (runOnly := [
      "checkType".toName,
      "checkUnivs".toName,
      "defLemma".toName,
      -- "docBlame".toName,
      -- "docBlameThm".toName,
      "dupNamespace".toName,
      "explicitVarsOfIff".toName,
      "impossibleInstance".toName,
      "nonClassInstance".toName,
      "simpComm".toName,
      "simpNF".toName,
      "simpVarHead".toName,
      "synTaut".toName,
      "unusedArguments".toName,
      "unusedHavesSuffices".toName
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
