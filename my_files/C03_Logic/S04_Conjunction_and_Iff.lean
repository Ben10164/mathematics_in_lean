import my_files.Common

namespace C03S04

example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬y ≤ x) : x ≤ y ∧ x ≠ y := by
  -- since it is an and statement, we can just prove both of the sides individually
  constructor
  -- case left : x ≤ y
  apply h₀
  -- case right : x ≠ y
  intro h -- x ≠ y -> x = y -> False
  -- if ¬(y ≤ x) → True, then we can replace False with y ≤ x
  apply h₁
  rw [h]

example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬y ≤ x) : x ≤ y ∧ x ≠ y :=
  -- lets construct x ≤ y ∧ x ≠ y
  ⟨h₀, -- x ≤ y
    fun h ↦           --intro h
      h₁              -- apply h
      (by rw [h])     -- rw [h]
  ⟩

example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬y ≤ x) : x ≤ y ∧ x ≠ y :=
  have h : x ≠ y := by
    contrapose! h₁ -- swap the state with h₁, negating both
    -- h₁ : ¬y ≤ x
    -- ⊢ x ≠ y
    -- becomes
    -- h₁ : x = y
    -- ⊢ y ≤ x
    rw [h₁]
  ⟨h₀, h⟩ -- construct it like before

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  rcases h with ⟨h₀, h₁⟩ -- decompose h into h₀ and h₁
  contrapose! h₁ -- swap with h₁
  apply le_antisymm
  apply h₀
  apply h₁

example {x y : ℝ} : x ≤ y ∧ x ≠ y → ¬y ≤ x := by
  rintro ⟨h₀, h₁⟩ h'
  apply h₁
  apply le_antisymm
  apply h₀
  apply h'

example {x y : ℝ} : x ≤ y ∧ x ≠ y → ¬y ≤ x :=
  fun ⟨h₀, h₁⟩ h' ↦ h₁ (le_antisymm h₀ h')

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  have ⟨h₀, h₁⟩ := h
  contrapose! h₁
  exact le_antisymm h₀ h₁

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  cases h -- extract h into left and right cases
  case intro h₀ h₁ => -- intro h₀ and h₁ and handle the cases
    contrapose! h₁
    exact le_antisymm h₀ h₁

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  cases h
  next h₀ h₁ =>
    contrapose! h₁
    exact le_antisymm h₀ h₁

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  match h with
    | ⟨h₀, h₁⟩ =>
        contrapose! h₁
        exact le_antisymm h₀ h₁

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  intro h'
  -- if the state is False, and it depends on an and, we can set the state to be equal to the right
  -- side of h negated
  apply h.right
  . apply le_antisymm
    apply h.left
    apply h'

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x :=
  fun h' ↦ h.right (le_antisymm h.left h')

example {m n : ℕ} (h : m ∣ n ∧ m ≠ n) : m ∣ n ∧ ¬n ∣ m := by
  cases h
  case intro h₀ h₁ =>
    . constructor
      apply h₀
      contrapose! h₁
      . apply dvd_antisymm -- turn `m = n` to proving `m | n` and `n | m`
        apply h₀
        apply h₁

example : ∃ x : ℝ, 2 < x ∧ x < 4 :=
  -- for this, we are basically just proving with an example
  ⟨3, by norm_num, by norm_num⟩
  -- define x as 3
  -- solve 2 < 3 using norm_num
  -- solve 3 < 4 using norm_num

example : ∃ x : ℝ, 2 < x ∧ x < 4 := by
  use 3 -- use 3 as x
  . constructor
    norm_num -- solves 2 < 3
    norm_num -- solves 3 < 4

example (x y : ℝ) : (∃ z : ℝ, x < z ∧ z < y) → x < y := by
  rintro ⟨z, xltz, zlty⟩
  exact lt_trans xltz zlty

example (x y : ℝ) : (∃ z : ℝ, x < z ∧ z < y) → x < y :=
  fun ⟨z, xltz, zlty⟩ ↦ lt_trans xltz zlty

example : ∃ x : ℝ, 2 < x ∧ x < 4 := by
  use 5 / 2
  constructor <;> norm_num

example : ∃ m n : ℕ, 4 < m ∧ m < n ∧ n < 10 ∧ Nat.Prime m ∧ Nat.Prime n := by
  use 5
  use 7
  norm_num

example {x y : ℝ} : x ≤ y ∧ x ≠ y → x ≤ y ∧ ¬y ≤ x := by
  rintro ⟨h₀, h₁⟩
  use h₀
  exact fun h' ↦ h₁ (le_antisymm h₀ h')

example {x y : ℝ} (h : x ≤ y) : ¬y ≤ x ↔ x ≠ y := by
  constructor
  · contrapose!
    rintro rfl
    rfl
  contrapose!
  exact le_antisymm h

example {x y : ℝ} (h : x ≤ y) : ¬y ≤ x ↔ x ≠ y :=
  ⟨fun h₀ h₁ ↦ h₀ (by rw [h₁]), fun h₀ h₁ ↦ h₀ (le_antisymm h h₁)⟩

example {x y : ℝ} : x ≤ y ∧ ¬y ≤ x ↔ x ≤ y ∧ x ≠ y := by
  constructor
  -- repeat
  . rintro ⟨h₀, h₁⟩
    constructor
    . apply h₀
    intro h₂
    apply h₁
    rw [h₂]
  rintro ⟨h₀, h₁⟩
  constructor
  . apply h₀
  intro h₂
  apply h₁
  apply le_antisymm
  apply h₀
  apply h₂

theorem aux {x y : ℝ} (h : x ^ 2 + y ^ 2 = 0) : x = 0 :=
  have h' : x ^ 2 = 0 := by
    apply le_antisymm
    . rw [← h]
      rw [le_add_iff_nonneg_right]
      rw [sq]
      apply mul_self_nonneg y
    apply pow_two_nonneg x

  pow_eq_zero h'

example (x y : ℝ) : x ^ 2 + y ^ 2 = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  . intro h
    constructor
    . apply aux at h
      apply h
    . rw [add_comm] at h
      apply aux at h
      apply h
  . intro ⟨xeqz,yeqz⟩
    rw [xeqz, yeqz]
    rw [zero_pow]
    rw [zero_add]
    norm_num

section

example (x : ℝ) : |x + 3| < 5 → -8 < x ∧ x < 2 := by
  rw [abs_lt]
  intro h
  constructor <;> linarith

example : 3 ∣ Nat.gcd 6 15 := by
  rw [Nat.dvd_gcd_iff]
  constructor <;> norm_num

end

theorem not_monotone_iff {f : ℝ → ℝ} : ¬Monotone f ↔ ∃ x y, x ≤ y ∧ f x > f y := by
  rw [Monotone]
  push_neg
  rfl

example : ¬Monotone fun x : ℝ ↦ -x := by
  rw [Monotone]
  push_neg
  use 0, 1
  constructor
  apply zero_le_one
  rw [neg_zero]
  apply neg_one_lt_zero

section
variable {α : Type*} [PartialOrder α]
variable (a b : α)

example : a < b ↔ a ≤ b ∧ a ≠ b := by
  rw [lt_iff_le_not_ge]
  constructor
  . intro ⟨aleb, nblea⟩
    rw [← lt_iff_le_and_ne]
    apply lt_of_le_not_ge aleb nblea
  . intro ⟨aleb, aneb⟩
    rw [← lt_iff_le_not_ge]
    apply lt_of_le_of_ne aleb aneb

end

section
variable {α : Type*} [Preorder α]
variable (a b c : α)

example : ¬a < a := by
  rw [lt_iff_le_not_ge]
  rw [not_and_not_right]
  intro alea
  apply alea

example : a < b → b < c → a < c := by
  simp only [lt_iff_le_not_ge]
  intro ⟨aleb, nblea⟩
  intro ⟨blec, ncleb⟩
  constructor
  . apply le_trans aleb blec
  . rintro clea
    apply nblea
    apply le_trans blec clea

end
