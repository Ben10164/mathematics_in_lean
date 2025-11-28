import my_files.Common

namespace C03S03

section
variable (a b : ℝ)

example (h : a < b) : ¬b < a := by
  intro h'
  have : a < a := by
    . apply lt_trans
      apply h
      apply h'
  apply lt_irrefl a this

-- a is the upper bound
def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

-- a is the lower bound
def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

-- Function has an upper bound
def FnHasUb (f : ℝ → ℝ) :=
  ∃ a, FnUb f a

-- Function has an lower bound
def FnHasLb (f : ℝ → ℝ) :=
  ∃ a, FnLb f a

variable (f : ℝ → ℝ)

example (h : ∀ a, ∃ x, f x > a) : ¬FnHasUb f := by
  intro fnub
  rcases fnub with ⟨a, fnuba⟩
  rcases h a with ⟨x, hx⟩
  have : f x ≤ a := fnuba x
  linarith

example (h : ∀ a, ∃ x, f x < a) : ¬FnHasLb f := by
  intro fnlb
  rcases fnlb with ⟨a, fnlba⟩
  rcases h a with ⟨x, hx⟩
  have : f x ≥ a := fnlba x
  linarith

example : ¬FnHasUb fun x ↦ x := by
  intro ⟨a, ha⟩
  have : a + 1 ≤ a := ha (a + 1)
  linarith

#check (not_le_of_gt : a > b → ¬a ≤ b)
#check (not_lt_of_ge : a ≥ b → ¬a < b)
#check (lt_of_not_ge : ¬a ≥ b → a < b)
#check (le_of_not_gt : ¬a > b → a ≤ b)

example (h : Monotone f) (h' : f a < f b) : a < b := by
  apply lt_of_not_ge
  intro h''
  apply absurd h'
  apply not_lt_of_ge
  apply h
  apply h''

example (h : a ≤ b) (h' : f b < f a) : ¬Monotone f := by
  intro h''
  apply absurd h'
  apply not_lt_of_ge
  apply h''
  apply h

example : ¬∀ {f : ℝ → ℝ}, Monotone f → ∀ {a b}, f a ≤ f b → a ≤ b := by
  intro h
  let f := fun x : ℝ ↦ (0 : ℝ)
  have monof : Monotone f := by
    intro c d cled
    rfl
  have h' : f 1 ≤ f 0 := by
    apply le_refl
  have : (1 : ℝ) ≤ 0 := by
    apply h
    apply monof
    apply h'
  apply absurd this
  apply not_le_of_gt
  apply zero_lt_one

example (x : ℝ) (h : ∀ ε > 0, x < ε) : x ≤ 0 := by
  apply le_of_not_gt
  intro h'
  apply absurd h'
  apply not_lt_of_ge
  /-
  case a.h
  a b : ℝ
  f : ℝ → ℝ
  x : ℝ
  h : ∀ ε > 0, x < ε
  h' : x > 0
  ⊢ x < 0
  -/
  -- there is a clear contradiction between h and h'
  linarith [h _ h']

end

section
variable {α : Type*} (P : α → Prop) (Q : Prop)

example (h : ¬∃ x, P x) : ∀ x, ¬P x := by
  intro x px
  apply h -- applies the ¬ portion since current state is false
  use x

example (h : ∀ x, ¬P x) : ¬∃ x, P x := by
  intro ⟨x,px⟩
  apply h x
  apply px

example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  by_contra h'
  /-
  α : Type u_1
  P : α → Prop
  Q : Prop
  h : ¬∀ (x : α), P x
  h' : ¬∃ x, ¬P x
  ⊢ False
  -/
  apply h
  /-
  α : Type u_1
  P : α → Prop
  Q : Prop
  h : ¬∀ (x : α), P x
  h' : ¬∃ x, ¬P x
  ⊢ ∀ (x : α), P x
  -/
  intro x
  /-
  α : Type u_1
  P : α → Prop
  Q : Prop
  h : ¬∀ (x : α), P x
  h' : ¬∃ x, ¬P x
  x : α
  ⊢ P x
  -/
  show P x
  by_contra h''
  /-
  α : Type u_1
  P : α → Prop
  Q : Prop
  h : ¬∀ (x : α), P x
  h' : ¬∃ x, ¬P x
  x : α
  h'' : ¬P x
  ⊢ False
  -/
  apply h'
  /-
  α : Type u_1
  P : α → Prop
  Q : Prop
  h : ¬∀ (x : α), P x
  h' : ¬∃ x, ¬P x
  x : α
  h'' : ¬P x
  ⊢ ∃ x, ¬P x
  -/
  exact ⟨x, h''⟩

example (h : ∃ x, ¬P x) : ¬∀ x, P x := by
  intro h'
  rcases h with ⟨a, nPa⟩
  apply nPa
  apply h' a

example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  by_contra h'
  apply h
  intro x
  show P x
  by_contra h''
  exact h' ⟨x, h''⟩

example (h : ¬¬Q) : Q := by
  . by_contra h'
    apply h
    apply h'

example (h : Q) : ¬¬Q := by
  by_contra h'
  apply h'
  apply h

end

section
variable (f : ℝ → ℝ)

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  intro a
  by_contra h'
  apply h
  use a
  intro x
  apply le_of_not_gt
  intro h''
  apply h'
  exact ⟨x, h''⟩

example (h : ¬∀ a, ∃ x, f x > a) : FnHasUb f := by
  push_neg at h
  exact h

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  dsimp only [FnHasUb, FnUb] at h
  push_neg at h
  exact h

example (h : ¬Monotone f) : ∃ x y, x ≤ y ∧ f y < f x := by
  rw [Monotone] at h
  push_neg at h
  exact h

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  contrapose! h
  exact h

example (x : ℝ) (h : ∀ ε > 0, x ≤ ε) : x ≤ 0 := by
  contrapose! h
  use x / 2
  constructor <;> linarith

end

section
variable (a : ℕ)

example (h : 0 < 0) : a > 37 := by
  exfalso
  apply lt_irrefl 0 h

example (h : 0 < 0) : a > 37 :=
  absurd h (lt_irrefl 0)

example (h : 0 < 0) : a > 37 := by
  have h' : ¬0 < 0 := lt_irrefl 0
  contradiction

end
