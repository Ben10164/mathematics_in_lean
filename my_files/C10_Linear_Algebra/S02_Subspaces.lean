import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.Tactic

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

example (U : Submodule K V) {x y : V} (hx : x ∈ U) (hy : y ∈ U) :
    x + y ∈ U :=
  U.add_mem hx hy

example (U : Submodule K V) {x : V} (hx : x ∈ U) (a : K) :
    a • x ∈ U :=
  U.smul_mem a hx


noncomputable example : Submodule ℝ ℂ where
  carrier := Set.range ((↑) : ℝ → ℂ)
  add_mem' := by
    rintro _ _ ⟨n, rfl⟩ ⟨m, rfl⟩
    use n + m
    simp
  zero_mem' := by
    use 0
    simp
  smul_mem' := by
    rintro c - ⟨a, rfl⟩
    use c*a
    simp


def preimage {W : Type*} [AddCommGroup W] [Module K W] (φ : V →ₗ[K] W) (H : Submodule K W) :
    Submodule K V where
  carrier := φ ⁻¹' H
  zero_mem' := by
    rw [Set.mem_preimage]
    rw [map_zero]
    exact H.zero_mem
  add_mem' := by
    simp
    rintro x y hx hy
    rw [Submodule.add_mem_iff_right H hx]
    apply hy
  smul_mem' := by
    simp
    rintro c x hx
    apply Submodule.smul_mem H c
    apply hx

example (U : Submodule K V) : Module K U := inferInstance

example (U : Submodule K V) : Module K {x : V // x ∈ U} := inferInstance

example (H H' : Submodule K V) :
    ((H ⊓ H' : Submodule K V) : Set V) = (H : Set V) ∩ (H' : Set V) := rfl

example (H H' : Submodule K V) :
    ((H ⊔ H' : Submodule K V) : Set V) = Submodule.span K ((H : Set V) ∪ (H' : Set V)) := by
  simp [Submodule.span_union]

example (x : V) : x ∈ (⊤ : Submodule K V) := trivial

example (x : V) : x ∈ (⊥ : Submodule K V) ↔ x = 0 := Submodule.mem_bot K


-- If two subspaces are in direct sum then they span the whole space.
example (U V : Submodule K V) (h : IsCompl U V) :
  U ⊔ V = ⊤ := h.sup_eq_top

-- If two subspaces are in direct sum then they intersect only at zero.
example (U V : Submodule K V) (h : IsCompl U V) :
  U ⊓ V = ⊥ := h.inf_eq_bot

section
open DirectSum
variable {ι : Type*} [DecidableEq ι]

-- If subspaces are in direct sum then they span the whole space.
example (U : ι → Submodule K V) (h : DirectSum.IsInternal U) :
  ⨆ i, U i = ⊤ := h.submodule_iSup_eq_top

-- If subspaces are in direct sum then they pairwise intersect only at zero.
example {ι : Type*} [DecidableEq ι] (U : ι → Submodule K V) (h : DirectSum.IsInternal U)
    {i j : ι} (hij : i ≠ j) : U i ⊓ U j = ⊥ :=
  (h.submodule_iSupIndep.pairwiseDisjoint hij).eq_bot

-- The relation with external direct sums: if a family of subspaces is
-- in internal direct sum then the map from their external direct sum into `V`
-- is a linear isomorphism.
noncomputable example {ι : Type*} [DecidableEq ι] (U : ι → Submodule K V)
    (h : DirectSum.IsInternal U) : (⨁ i, U i) ≃ₗ[K] V :=
  LinearEquiv.ofBijective (coeLinearMap U) h
end

example {s : Set V} (E : Submodule K V) : Submodule.span K s ≤ E ↔ s ⊆ E :=
  Submodule.span_le

example : GaloisInsertion (Submodule.span K) ((↑) : Submodule K V → Set V) :=
  Submodule.gi K V

example {S T : Submodule K V} {x : V} (h : x ∈ S ⊔ T) :
    ∃ s ∈ S, ∃ t ∈ T, x = s + t  := by
  rw [← S.span_eq, ← T.span_eq, ← Submodule.span_union] at h
  induction h using Submodule.span_induction with
  | mem y h =>
      rcases h with (hy|hy)
      .
        -- we know y ∈ S, so we can simply use y for s
        use y
        use hy
        -- after this we then need to find a value for which y + _ = y
        -- obviously this is zero
        use 0
        -- but we still need to prove that 0 ∈ T
        -- we can use the theorem that all AddComm ring types
        -- contain a additive identity (0) to prove that 0 ∈ T
        use T.zero_mem
        rw [AddZeroClass.add_zero y]
      .
        -- this one is the same as the previous one, but we are starting with
        -- the value which ∈ T, which we know is zero
        use 0
        use S.zero_mem
        use y
        use hy
        rw [AddZeroClass.zero_add y]
  | zero =>
      -- this one is just proving that zero is a thing
      use 0
      use S.zero_mem
      use 0
      use T.zero_mem
      rw [AddZeroClass.zero_add 0]
  | add x y hx hy hx' hy' =>
      -- rcases hx' with ⟨s, hs, t, ht, tttt⟩
      rcases hx' with ⟨s, hs, t, ht, xst⟩
      rcases hy' with ⟨s', hs', t', ht', ys't'⟩
      -- rw [xst] -- reminder that x = s + t
      -- rw [ys't'] -- reminder that y = s' + t'
      -- with this reminder, we can rewrite x + y = s'' + t'' (added '' to distinguish them)
      -- as s + t + s' + t' = s + t
      use s + s'
      constructor
      . apply S.add_mem
        apply hs
        apply hs'
      use t + t'
      constructor
      . apply T.add_mem
        apply ht
        apply ht'
      rw [xst]
      rw [ys't']
      rw [← add_assoc (s + t) s' t']
      rw [add_comm s t]
      rw [add_assoc t s s']
      rw [add_comm t (s + s')]
      rw [← add_assoc (s + s') t t']
  | smul a x hx hx' =>
      -- lets extract the expressions contained in hx'
      -- hx' : ∃ s ∈ S, ∃ t ∈ T, x = s + t
      rcases hx' with ⟨
        s, -- V
        hs, -- s ∈ S
        t, -- V
        ht, -- t ∈ T
        xst -- x = s + t
      ⟩
      -- we are trying to show that for any product, there exists 2 numbers that can be added
      -- to get that number
      use a • s
      constructor
      . apply S.smul_mem
        apply hs
      use a • t
      constructor
      . apply T.smul_mem
        apply ht
      rw [xst]
      rw [smul_add]

section

variable {W : Type*} [AddCommGroup W] [Module K W] (φ : V →ₗ[K] W)

variable (E : Submodule K V) in
#check (Submodule.map φ E : Submodule K W)

variable (F : Submodule K W) in
#check (Submodule.comap φ F : Submodule K V)

example : LinearMap.range φ = .map φ ⊤ := LinearMap.range_eq_map φ

example : LinearMap.ker φ = .comap φ ⊥ := Submodule.comap_bot φ -- or `rfl`



open Function LinearMap

example : Injective φ ↔ ker φ = ⊥ := ker_eq_bot.symm

example : Surjective φ ↔ range φ = ⊤ := range_eq_top.symm

#check Submodule.mem_map_of_mem
#check Submodule.mem_map
#check Submodule.mem_comap

example (E : Submodule K V) (F : Submodule K W) :
    Submodule.map φ E ≤ F ↔ E ≤ Submodule.comap φ F := by
  constructor
  · intro h x hx
    apply h
    apply Submodule.mem_map_of_mem
    apply hx
  . rintro h _ ⟨x, hx, xeq⟩
    rw [← Submodule.mem_toAddSubgroup F]
    rw [← xeq]
    apply h
    apply hx

variable (E : Submodule K V)

example : Module K (V ⧸ E) := inferInstance

example : V →ₗ[K] V ⧸ E := E.mkQ

example : ker E.mkQ = E := E.ker_mkQ

example : range E.mkQ = ⊤ := E.range_mkQ

example (hφ : E ≤ ker φ) : V ⧸ E →ₗ[K] W := E.liftQ φ hφ

example (F : Submodule K W) (hφ : E ≤ .comap φ F) : V ⧸ E →ₗ[K] W ⧸ F := E.mapQ F φ hφ

noncomputable example : (V ⧸ LinearMap.ker φ) ≃ₗ[K] range φ := φ.quotKerEquivRange


open Submodule

#check Submodule.map_comap_eq
#check Submodule.comap_map_eq

example : Submodule K (V ⧸ E) ≃ { F : Submodule K V // E ≤ F } where
  toFun F :=
    ⟨comap E.mkQ F, by
      apply le_comap_mkQ E F
      -- conv_lhs =>
        -- rw [← E.ker_mkQ]
        -- rw [← comap_bot]
      -- gcongr
      -- apply bot_le
    ⟩
  invFun := by
    intro P
    apply map E.mkQ P
  left_inv := by
    intro P
    dsimp
    rw [Submodule.map_comap_eq E.mkQ P]
    rw [range_mkQ E]
    apply top_inf_eq P
  right_inv := by
    intro P
    ext x
    dsimp
    rw [Submodule.comap_map_eq]
    rw [E.ker_mkQ]
    rw [sup_of_le_left]
    apply P.2
