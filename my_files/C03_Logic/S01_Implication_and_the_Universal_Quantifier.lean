import my_files.Common

namespace C03S01

#check ∀ x : ℝ, 0 ≤ x → |x| = x

#check ∀ x y ε : ℝ, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε

-- Same as before, but this one declares x y and ε directly
theorem my_lemma : ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
  -- now we use intro to introduce all the variables as well as the statements
  intro x y ε epos ele1 xlt ylt
  /-
  x → x
  y → y
  ε → ε
  epos → 0 < ε
  ele1 → ε ≤ 1
  xlt → |x| < ε
  ylt → |y| < ε
  -/
  calc
    |x * y| = |x| * |y| := by
      apply abs_mul
    _ ≤ |x| * ε := by
      . apply mul_le_mul
        . apply le_refl
        . apply le_of_lt
          apply ylt
        . apply abs_nonneg
        . apply abs_nonneg
    _ < 1 * ε := by
      . rw [mul_lt_mul_right]
        . apply lt_of_lt_of_le xlt
          apply ele1
        . apply epos
    _ = ε := by
      apply one_mul

section
variable (a b δ : ℝ)
variable (h₀ : 0 < δ) (h₁ : δ ≤ 1)
variable (ha : |a| < δ) (hb : |b| < δ)

#check my_lemma
#check my_lemma h₀ h₁
#check my_lemma h₀ h₁ ha hb

end

def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

#check FnUb

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

#check FnLb

section
variable (f g : ℝ → ℝ) (a b : ℝ)

example (hfa : FnUb f a) (hgb : FnUb g b) : FnUb (fun x ↦ f x + g x) (a + b) := by
  intro x
  dsimp
  apply add_le_add
  apply hfa
  apply hgb

example (hfa : FnLb f a) (hgb : FnLb g b) : FnLb (fun x ↦ f x + g x) (a + b) := by
  intro x
  dsimp
  . apply add_le_add
    . apply hfa
    . apply hgb

example (nnf : FnLb f 0) (nng : FnLb g 0) : FnLb (fun x ↦ f x * g x) 0 := by
  intro x
  dsimp
  . apply mul_nonneg
    . apply nnf
    . apply nng

example (hfa : FnUb f a) (hgb : FnUb g b) (nng : FnLb g 0) (nna : 0 ≤ a) :
    FnUb (fun x ↦ f x * g x) (a * b) := by
      intro x
      dsimp
      . apply mul_le_mul
        . apply hfa
        . apply hgb
        . apply nng
        . apply nna

end

section
variable {α : Type*} {R : Type*} [AddCommMonoid R] [PartialOrder R] [IsOrderedCancelAddMonoid R]

#check add_le_add

def FnUb' (f : α → R) (a : R) : Prop :=
  ∀ x, f x ≤ a

theorem fnUb_add {f g : α → R} {a b : R} (hfa : FnUb' f a) (hgb : FnUb' g b) :
    FnUb' (fun x ↦ f x + g x) (a + b) := fun x ↦ add_le_add (hfa x) (hgb x)

end

example (f : ℝ → ℝ) (h : Monotone f) : ∀ {a b}, a ≤ b → f a ≤ f b :=
  @h

section
variable (f g : ℝ → ℝ)

-- same as
example (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f x + g x := by
  intro a b aleb
  dsimp
  . apply add_le_add
    . apply mf
      apply aleb
    . apply mg
      apply aleb
-- same as
example (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f x + g x :=
  fun a b aleb ↦ add_le_add (mf aleb) (mg aleb)

example {c : ℝ} (mf : Monotone f) (nnc : 0 ≤ c) : Monotone fun x ↦ c * f x := by
  intro a b aleb
  dsimp
  . apply mul_le_mul_of_nonneg_left
    . apply mf
      apply aleb
    apply nnc
-- same as
example {c : ℝ} (mf : Monotone f) (nnc : 0 ≤ c) : Monotone fun x ↦ c * f x :=
  fun a b aleb ↦ mul_le_mul_of_nonneg_left (mf aleb) (nnc)

example (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f (g x) := by
  intro a b aleb
  dsimp
  apply mf
  . apply mg
    apply aleb
-- same as
example (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f (g x) :=
  fun a b aleb ↦ mf (mg aleb)

def FnEven (f : ℝ → ℝ) : Prop :=
  ∀ x, f x = f (-x)

def FnOdd (f : ℝ → ℝ) : Prop :=
  ∀ x, f x = -f (-x)

example (ef : FnEven f) (eg : FnEven g) : FnEven fun x ↦ f x + g x := by
  intro x
  calc
    (fun x ↦ f x + g x) x = f x + g x := rfl
    _ = f (-x) + g (-x) := by rw [ef, eg]

example (of : FnOdd f) (og : FnOdd g) : FnEven fun x ↦ f x * g x := by
  intro x
  calc
    (fun x ↦ f x * g x) x = f x * g x := by
      rfl
    _ = f (-x) * g (-x) := by
      rw [of]
      rw [og]
      rw [neg_mul_neg]

example (ef : FnEven f) (og : FnOdd g) : FnOdd fun x ↦ f x * g x := by
  intro x
  dsimp
  rw [ef]
  rw [og]
  rw [neg_mul_eq_mul_neg]

example (ef : FnEven f) (og : FnOdd g) : FnEven fun x ↦ f (g x) := by
  intro x
  dsimp
  rw [og]
  rw [← ef]

end

section

variable {α : Type*} (r s t : Set α)

example : s ⊆ s := by
  intro x xs
  exact xs

theorem Subset.refl : s ⊆ s :=
  fun _ xs ↦ xs

theorem Subset.trans : r ⊆ s → s ⊆ t → r ⊆ t :=
  fun rsubs ssubt _ xr ↦ ssubt (rsubs xr)

end

section
variable {α : Type*} [PartialOrder α]
variable (s : Set α) (a b : α)

def SetUb (s : Set α) (a : α) :=
  ∀ x, x ∈ s → x ≤ a

example (h : SetUb s a) (h' : a ≤ b) : SetUb s b := by
  intro x xs
  . apply le_trans
    apply h x
    apply xs
    apply h'

end

section

open Function

set_option linter.unusedTactic false

example (c : ℝ) : Injective fun x ↦ x + c := by
  -- ∀ ⦃a₂ : ℝ⦄, (fun x => x + c) a₁✝ = (fun x => x + c) a₂ → a₁✝ = a₂
  intro
    x₁ -- a₁
    x₂ -- a₂
    h' -- (fun x => x + c) x₁ = (fun x => x + c) x₂)
  -- x₁ = x₂
  #check add_left_inj c
  #check (add_left_inj c).mp
  -- ^ this is what we want (way to go from x₁ = x₂ to what h' is)
  apply (add_left_inj c).mp
  apply h'

example {c : ℝ} (h : c ≠ 0) : Injective fun x ↦ c * x := by
  intro x₁ x₂ h'
  #check mul_right_inj' h
  #check (mul_right_inj' h).mp
  apply (mul_right_inj' h).mp
  apply h'

variable {α : Type*} {β : Type*} {γ : Type*}
variable {g : β → γ} {f : α → β}

example (injg : Injective g) (injf : Injective f) : Injective fun x ↦ g (f x) := by
  intro x₁ x₂ h
  -- we want to turn `x₁ = x₂` into `g (f x₁) = g (f x₂)`
  apply injf -- `f x₁ = f x₂`
  apply injg -- `g (f x₁) = g (f x₂)`
  apply h

end
