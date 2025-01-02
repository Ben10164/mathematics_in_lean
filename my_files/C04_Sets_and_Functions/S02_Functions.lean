import MIL.Common
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Analysis.SpecialFunctions.Log.Basic

section

variable {α β : Type*}
variable (f : α → β)
variable (s t : Set α)
variable (u v : Set β)

open Function
open Set

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v := by
  ext
  rfl

example : f '' (s ∪ t) = f '' s ∪ f '' t := by
  ext y; constructor
  · rintro ⟨x, xs | xt, rfl⟩
    · left
      use x, xs
    right
    use x, xt
  rintro (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩)
  · use x, Or.inl xs
  use x, Or.inr xt

example : s ⊆ f ⁻¹' (f '' s) := by
  intro x xs
  show f x ∈ f '' s
  use x, xs

example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  apply image_subset_iff

example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  apply preimage_subset
  . intro x xs
    apply xs
  . intro x _ y _ xeqy
    apply h xeqy

example : f '' (f ⁻¹' u) ⊆ u := by
  apply image_preimage_subset

example (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
  apply mem_of_eq_of_mem
  rw [Surjective.image_preimage h u]
  intro x xs
  apply xs

example (h : s ⊆ t) : f '' s ⊆ f '' t := by
  apply mem_of_eq_of_mem
  apply rfl
  intro x xs
  apply mem_of_mem_of_subset xs
  apply image_mono h

example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := by
  intro x xs
  apply h
  apply xs

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
  ext x
  rfl

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  rintro y ⟨x, ⟨xs, xt⟩, rfl⟩
  constructor
  . apply mem_image_of_mem
    apply xs
  . apply mem_image_of_mem
    apply xt

example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  intro y ⟨⟨x₁,x₁s,fx₁eq⟩, ⟨x₂,x₂t,fx₂eq⟩⟩
  have fx₁eqfx₂ : f x₁ = f x₂ := by
    rw [fx₁eq]
    rw [fx₂eq]
  use x₁
  constructor
  . constructor
    . apply x₁s
    . rw [h fx₁eqfx₂]
      apply x₂t
  . apply fx₁eq

example : f '' s \ f '' t ⊆ f '' (s \ t) := by
  intro y ⟨⟨x₁,x₁s,fx₁eq⟩, yneq⟩
  use x₁
  constructor
  . constructor
    . apply x₁s
    . intro yeq
      apply yneq
      use x₁
  . apply fx₁eq

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) := by
  exact fun x ↦ id

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by
  ext y
  constructor
  · rintro ⟨⟨x, xs, fxeq⟩, yv⟩
    use x
    constructor
    . use xs
      apply mem_of_eq_of_mem fxeq
      apply yv
    . apply fxeq
  rintro ⟨x, ⟨⟨xs, fxv⟩, fxeq⟩⟩
  constructor
  . use x
  . apply mem_of_eq_of_mem fxeq.symm
    apply fxv

example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u := by
  intro y ⟨x, ⟨xs, fxu⟩,fxeq⟩
  constructor
  . use x
  . apply mem_of_eq_of_mem fxeq.symm
    apply fxu

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by
  intro x ⟨xs, fxu⟩
  constructor
  . apply mem_image_of_mem
    apply xs
  . apply fxu

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
  rintro x (xs | fxu)
  . left
    apply mem_image_of_mem f xs
  . right
    apply fxu

variable {I : Type*} (A : I → Set α) (B : I → Set β)

example : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
  ext y
  simp
  constructor
  · intro ⟨x, ⟨i, xAi⟩, fxeq⟩
    use i, x
  intro ⟨i, x, xAi, fxeq⟩
  use x
  use ⟨i, xAi⟩

example : (f '' ⋂ i, A i) ⊆ ⋂ i, f '' A i := by
  intro y
  simp
  intro x h fxeq i
  use x
  constructor
  . apply h
  . apply fxeq

example (i : I) (injf : Injective f) : (⋂ i, f '' A i) ⊆ f '' ⋂ i, A i := by
  intro y
  simp
  intro h
  rcases h i with ⟨x, xAi, fxeq⟩
  use x
  constructor
  · intro i'
    rcases h i' with ⟨x', x'Ai, fx'eq⟩
    have fxeqfx' : f x = f x' := by
      rw [fxeq, fx'eq]
    have : x = x' := by
      apply injf fxeqfx'
    rw [this]
    apply x'Ai
  . apply fxeq

example : (f ⁻¹' ⋃ i, B i) = ⋃ i, f ⁻¹' B i := by
  ext x
  simp

example : (f ⁻¹' ⋂ i, B i) = ⋂ i, f ⁻¹' B i := by
  ext x
  simp

example : InjOn f s ↔ ∀ x₁ ∈ s, ∀ x₂ ∈ s, f x₁ = f x₂ → x₁ = x₂ :=
  Iff.refl _

end

section

open Set Real

example : InjOn log { x | x > 0 } := by
  intro x xpos y ypos
  intro e
  -- log x = log y
  calc
    x = exp (log x) := by rw [exp_log xpos]
    _ = exp (log y) := by rw [e]
    _ = y := by rw [exp_log ypos]


example : range exp = { y | y > 0 } := by
  ext y; constructor
  · rintro ⟨x, rfl⟩
    apply exp_pos
  intro ypos
  use log y
  rw [exp_log ypos]

example : InjOn sqrt { x | x ≥ 0 } := by
  intro x xnonneg y ynonneg
  intro e
  calc
    x = sqrt x ^ 2 := by
      rw [sq_sqrt]
      apply xnonneg
    _ = sqrt y ^ 2 := by
      rw [e]
    _ = y := by
      rw [sq_sqrt]
      apply ynonneg

example : InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } := by
  intro x xnonneg y ynonneg
  intro e
  dsimp at *
  calc
    x = sqrt (x ^ 2) := by
      rw [sqrt_sq]
      apply xnonneg
    _ = sqrt (y ^ 2) := by
      rw [e]
    _ = y := by
      rw [sqrt_sq]
      apply ynonneg

example : sqrt '' { x | x ≥ 0 } = { y | y ≥ 0 } := by
  ext y
  constructor
  . rintro ⟨x, ⟨xnonneg, sqrtxeqy⟩⟩
    rw [← sqrtxeqy]
    apply sqrt_nonneg
  . intro ynonneg
    use y ^ 2
    dsimp at *
    constructor
    . apply sq_nonneg
    . apply sqrt_sq
      apply ynonneg

example : (range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by
  ext y
  constructor
  . rintro ⟨x, ⟨y, sqyeqx⟩⟩
    dsimp
    apply sq_nonneg
  . intro ynonneg
    use sqrt y
    apply sq_sqrt
    apply ynonneg

end

section
variable {α β : Type*} [Inhabited α]

#check (default : α)

variable (P : α → Prop) (h : ∃ x, P x)

#check Classical.choose h

example : P (Classical.choose h) :=
  Classical.choose_spec h

noncomputable section

open Classical

def inverse (f : α → β) : β → α := fun y : β ↦
  if h : ∃ x, f x = y then Classical.choose h else default

theorem inverse_spec {f : α → β} (y : β) (h : ∃ x, f x = y) : f (inverse f y) = y := by
  rw [inverse, dif_pos h]
  exact Classical.choose_spec h

variable (f : α → β)

open Function

example : Injective f ↔ LeftInverse (inverse f) f := by
  constructor
  · intro h y
    apply h
    apply inverse_spec
    use y
  intro h x1 x2 e
  rw [← h x1, ← h x2, e]

example : Surjective f ↔ RightInverse (inverse f) f := by
  constructor
  · intro h y
    apply inverse_spec
    apply h
  intro h y
  use inverse f y
  apply h

end

section
variable {α : Type*}
open Function

theorem Cantor : ∀ f : α → Set α, ¬Surjective f := by
  intro f surjf
  let S := { i | i ∉ f i }
  rcases surjf S with ⟨j, h⟩
  have h₁ : j ∉ f j := by
    intro h'
    have : j ∉ f j := by rwa [h] at h'
    contradiction
  have h₂ : j ∈ S := by
    apply h₁
  have h₃ : j ∉ S := by
    rw [h] at h₁
    apply h₁
  contradiction

end
