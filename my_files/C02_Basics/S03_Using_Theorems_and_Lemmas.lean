import MIL.Common

set_option linter.unusedTactic false

variable (a b c d e : ℝ)
open Real

#check (le_refl : ∀ a : ℝ, a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)

section
variable (h : a ≤ b) (h' : b ≤ c)

#check (le_refl : ∀ a : Real, a ≤ a)
#check (le_refl a : a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)
#check (le_trans h : b ≤ c → a ≤ c)
#check (le_trans h h' : a ≤ c)

end

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
  apply le_trans
  · apply h₀
  · apply h₁

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
  apply le_trans h₀
  apply h₁

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z :=
  le_trans h₀ h₁

example (x : ℝ) : x ≤ x := by
  apply le_refl

example (x : ℝ) : x ≤ x :=
  le_refl x

#check (le_refl : ∀ a, a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)
#check (lt_of_le_of_lt : a ≤ b → b < c → a < c)
#check (lt_of_lt_of_le : a < b → b ≤ c → a < c)
#check (lt_trans : a < b → b < c → a < c)

-- Try this.
example (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by
  apply lt_trans (lt_of_le_of_lt h₀ h₁) (lt_of_le_of_lt h₂ h₃)

example (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by
  linarith -- linear arithmatic

section

example (h : 2 * a ≤ 3 * b) (h' : 1 ≤ a) (h'' : d = 2) : d + a ≤ 5 * b := by
  linarith

end

-- exp x is e^x
-- exp_le_exp.mr is a proof for exp b <= exp c if and only if b <= c
-- (mpr is modus ponens, if and only if)
example (h : 1 ≤ a) (h' : b ≤ c) : 2 + a + exp b ≤ 3 * a + exp c := by
  linarith [exp_le_exp.mpr h']

#check (exp_le_exp : exp a ≤ exp b ↔ a ≤ b)
#check exp_le_exp
#check (exp_lt_exp : exp a < exp b ↔ a < b)
#check (log_le_log : 0 < a → a ≤ b → log a ≤ log b)
#check (log_lt_log : 0 < a → a < b → log a < log b)
#check (add_le_add : a ≤ b → c ≤ d → a + c ≤ b + d)
#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
#check (add_le_add_right : a ≤ b → ∀ c, a + c ≤ b + c)
#check (add_lt_add_of_le_of_lt : a ≤ b → c < d → a + c < b + d)
#check (add_lt_add_of_lt_of_le : a < b → c ≤ d → a + c < b + d)
#check (add_lt_add_left : a < b → ∀ c, c + a < c + b)
#check (add_lt_add_right : a < b → ∀ c, a + c < b + c)
#check (add_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a + b)
#check (add_pos : 0 < a → 0 < b → 0 < a + b)
#check (add_pos_of_pos_of_nonneg : 0 < a → 0 ≤ b → 0 < a + b)
#check (exp_pos : ∀ a, 0 < exp a)
#check add_le_add_left

example (h : a ≤ b) : exp a ≤ exp b := by
  rw [exp_le_exp]
  -- now its a ≤ b
  apply h

example (h₀ : a ≤ b) (h₁ : c < d) : a + exp c + e < b + exp d + e := by
  apply add_lt_add_of_lt_of_le
  · apply add_lt_add_of_le_of_lt h₀
    apply exp_lt_exp.mpr h₁
  apply le_refl

example (h₀ : d ≤ e) : c + exp (a + d) ≤ c + exp (a + e) := by
  apply add_le_add_left
  rw [exp_le_exp]
  rw [add_comm a d, add_comm a e]
  apply add_le_add
  apply h₀
  apply le_refl

example : (0 : ℝ) < 1 := by norm_num

example (h : a ≤ b) : log (1 + exp a) ≤ log (1 + exp b) := by
  have h₀ : 0 < 1 + exp a := by
    apply add_pos_of_pos_of_nonneg
    linarith -- solve case ha
    linarith [exp_pos a]
  apply log_le_log h₀
  apply add_le_add_left
  rw [exp_le_exp]
  exact h

example : 0 ≤ a ^ 2 := by
  -- apply?
  exact sq_nonneg a

example (h : a ≤ b) : c - exp b ≤ c - exp a := by
  apply sub_le_sub_left
  rw [exp_le_exp]
  exact h

example : 2 * a * b ≤ a ^ 2 + b ^ 2 := by
  have h : 0 ≤ a ^ 2 - 2 * a * b + b ^ 2
  calc
    a ^ 2 - 2 * a * b + b ^ 2 = (a - b) ^ 2 := by ring
    _ ≥ 0 := by apply pow_two_nonneg

  calc
    2 * a * b = 2 * a * b + 0 := by ring
    _ ≤ 2 * a * b + (a ^ 2 - 2 * a * b + b ^ 2) := add_le_add (le_refl _) h
    _ = a ^ 2 + b ^ 2 := by ring

example : 2 * a * b ≤ a ^ 2 + b ^ 2 := by
  have h : 0 ≤ a ^ 2 - 2 * a * b + b ^ 2
  calc
    a ^ 2 - 2 * a * b + b ^ 2 = (a - b) ^ 2 := by ring
    _ ≥ 0 := by apply pow_two_nonneg
  linarith

example : |a * b| ≤ (a ^ 2 + b ^ 2) / 2 := by
  -- We are going to be using abs_le' for this
  #check abs_le'.mpr
  apply abs_le'.mpr
  -- ⊢ a * b ≤ (a ^ 2 + b ^ 2) / 2 ∧ -(a * b) ≤ (a ^ 2 + b ^ 2) / 2

  -- Lets multiply both sides by 2 to get rid of that /2
  -- lets make a nice prop that states that 0 < 2 so we can use the previous tactic
  have h₀ : (0 : ℝ) < 2 := by
    norm_num
  -- Now we can do this
  #check le_div_iff₀ h₀

  rw [le_div_iff₀ h₀]
  rw [le_div_iff₀ h₀]

  -- So lets do both sides of the or (but multiplied by 2 because division is lame)
  have h₁: a * b * 2 ≤ a^2 + b^2 := by linarith [
    calc
      a^2 - 2 * a * b + b^2 = (a - b)^2 := by
        ring
      _ ≥ 0 := by
        apply pow_two_nonneg
  ]
  have h₂ : -(a * b) * 2 ≤ a^2 + b^2 := by linarith [
    calc
      a^2 + 2 * a * b + b^2 = (a + b)^2 := by
        ring
      _ ≥ 0 := by
        apply pow_two_nonneg
  ]

  -- constructor is a way to prove sides of a goal, in this case an AND with a left and right
  -- so it is breaking the main goal (x ^ y) into left (x) and right (y)
  constructor
    -- left
  . apply h₁
  -- right
  apply h₂
