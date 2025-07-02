import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Charpoly.Basic

import my_files.Common

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

variable {W : Type*} [AddCommGroup W] [Module K W]


open Polynomial Module LinearMap

example (φ ψ : End K V) : φ * ψ = φ ∘ₗ ψ :=
  End.mul_eq_comp φ ψ

-- evaluating `P` on `φ`
example (P : K[X]) (φ : End K V) : V →ₗ[K] V :=
  aeval φ P

-- evaluating `X` on `φ` gives back `φ`
example (φ : End K V) : aeval φ (X : K[X]) = φ :=
  aeval_X φ


#check Submodule.eq_bot_iff
-- p = ⊥ ↔ ∀ x ∈ p, x = 0
#check Submodule.mem_inf
-- x ∈ p ⊓ q ↔ x ∈ p ∧ x ∈ q
#check LinearMap.mem_ker
-- y ∈ ker f ↔ f y = 0

example (P Q : K[X]) (h : IsCoprime P Q) (φ : End K V) :
    ker (aeval φ P) ⊓ ker (aeval φ Q) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  -- ⊢ ∀ x ∈ ker ((aeval φ) P) ⊓ ker ((aeval φ) Q), x = 0
  rintro x
  rw [Submodule.mem_inf]
  -- ⊢ x ∈ ker ((aeval φ) P) ∧ x ∈ ker ((aeval φ) Q) → x = 0
  rw [mem_ker, mem_ker]
  -- ⊢ ((aeval φ) P) x = 0 ∧ ((aeval φ) Q) x = 0 → x = 0

  rintro ⟨hx, hy⟩
  rcases h with ⟨A, B, hAB⟩
  -- IsCoprime P Q ⇒ A B : K[X], hAB : A * P + B * Q = 1

  -- congr: Congruency
  -- h : a = b then congr(1 + $h) : 1 + a = 1 + b
  -- we have A * P + B * Q = 1, and we want to make an aeval φ _ x for both sides
  -- then we can expand and simplify values to 0
  have := congr(((aeval φ) $hAB.symm) x)
  -- ((aeval φ) 1) x = ((aeval φ) (A * P + B * Q)) x

  -- lets simplify *this* to be only x on the left side
  -- this : ((aeval φ) 1) x = ((aeval φ) (A * P + B * Q)) x
  rw [map_one] at this
  -- this : 1 x = ((aeval φ) (A * P + B * Q)) x
  rw [End.one_apply] at this
  -- this : x = ((aeval φ) (A * P + B * Q)) x

  -- now we can rewrite x
  rw [this]
  -- ⊢ ((aeval φ) (A * P + B * Q)) x = 0

  -- now for a whole lot of expanding
  rw [map_add]
  -- ⊢ ((aeval φ) (A * P) + (aeval φ) (B * Q)) x = 0
  rw [map_mul, map_mul]
  -- ⊢ ((aeval φ) A * (aeval φ) P + (aeval φ) B * (aeval φ) Q) x = 0
  rw [add_apply]
  -- ⊢ ((aeval φ) A * (aeval φ) P) x + ((aeval φ) B * (aeval φ) Q) x = 0
  rw [End.mul_apply, End.mul_apply]
  -- ⊢ ((aeval φ) A) (((aeval φ) P) x) + ((aeval φ) B) (((aeval φ) Q) x) = 0

  -- now that we are totally expanded, we can use hx and hy to simplify down to 0 for some
  rw [hx]
  rw [hy]

  -- since it is aeval _ _ 0, that is always 0, so we can reduce there
  rw [map_zero, map_zero]

  -- 0 + 0 = 0 is trivial
  rw [add_eq_left]


#check Submodule.add_mem_sup
#check map_mul
#check End.mul_apply
#check LinearMap.ker_le_ker_comp

example (P Q : K[X]) (h : IsCoprime P Q) (φ : End K V) :
    ker (aeval φ P) ⊔ ker (aeval φ Q) = ker (aeval φ (P*Q)) := by
  apply le_antisymm
  -- ⊢ ker ((aeval φ) P) ⊔ ker ((aeval φ) Q) ≤ ker ((aeval φ) (P * Q))
  . apply sup_le
      -- ⊢ ker ((aeval φ) P) ≤ ker ((aeval φ) (P * Q))
      -- we want to use ker_le_ker_comp (ker f ≤ ker (g ∘ₛₗ f))
      -- so lets go through the two goals
    .
      -- ker ((aeval φ) P) ≤ ker ((aeval φ) (P * Q))
      -- lets swap the P and Q, because we want it to be in the order f g f
      rw [mul_comm]
      -- ⊢ ker ((aeval φ) P) ≤ ker ((aeval φ) (Q * P))
      -- now we expand that aeval
      rw [map_mul]
      -- ker ((aeval φ) P) ≤ ker ((aeval φ) Q * (aeval φ) P)
      apply LinearMap.ker_le_ker_comp ((aeval φ) P) ((aeval φ) Q)
    .
      -- ⊢ ker ((aeval φ) Q) ≤ ker ((aeval φ) (P * Q))
      -- same as above, but we dont need to do the mul_comm since they are already
      -- in the right order
      rw[map_mul]
      apply LinearMap.ker_le_ker_comp
  -- time for something similar to earlier...
  . intro x hx
    rcases h with ⟨U, V, hUV⟩

    have breakdown : x = aeval φ (U*P) x + aeval φ (V*Q) x := by
      -- have := congr((aeval φ) $hUV.symm x)
      have : (((aeval φ) 1) x) = (((aeval φ) (U * P + V * Q)) x) := congr((aeval φ) $hUV.symm x)

      rw [map_one] at this
      rw [End.one_apply] at this
      rw [map_add] at this
      apply this
    rw [breakdown]
    rw [add_comm]
    apply Submodule.add_mem_sup
    -- <;>
    . rw [mem_ker]
      rw [← End.mul_apply]
      rw [← map_mul]
      have : P*(V*Q) = V*(P*Q) := by
        rw [mul_left_comm]
      rw [this]
      rw [map_mul]
      rw [End.mul_apply]
      rw [hx]
      rw [map_zero]
    . rw [mem_ker]
      rw [← End.mul_apply]
      rw [← map_mul]
      have : Q*(U*P) = U*(P*Q) := by
        rw [mul_left_comm]
        rw [mul_comm Q P]
      rw [this]
      rw [map_mul]
      rw [End.mul_apply]
      rw [hx]
      rw [map_zero]


example (φ : End K V) (a : K) : φ.eigenspace a = LinearMap.ker (φ - a • 1) :=
  End.eigenspace_def



example (φ : End K V) (a : K) : φ.HasEigenvalue a ↔ φ.eigenspace a ≠ ⊥ :=
  Iff.rfl

example (φ : End K V) (a : K) : φ.HasEigenvalue a ↔ ∃ v, φ.HasEigenvector a v  :=
  ⟨End.HasEigenvalue.exists_hasEigenvector, fun ⟨_, hv⟩ ↦ φ.hasEigenvalue_of_hasEigenvector hv⟩

example (φ : End K V) : φ.Eigenvalues = {a // φ.HasEigenvalue a} :=
  rfl

-- Eigenvalue are roots of the minimal polynomial
example (φ : End K V) (a : K) : φ.HasEigenvalue a → (minpoly K φ).IsRoot a :=
  φ.isRoot_of_hasEigenvalue

-- In finite dimension, the converse is also true (we will discuss dimension below)
example [FiniteDimensional K V] (φ : End K V) (a : K) :
    φ.HasEigenvalue a ↔ (minpoly K φ).IsRoot a :=
  φ.hasEigenvalue_iff_isRoot

-- Cayley-Hamilton
example [FiniteDimensional K V] (φ : End K V) : aeval φ φ.charpoly = 0 :=
  φ.aeval_self_charpoly
