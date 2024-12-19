import Mathlib.Data.Nat.Prime.Defs

open Bool Subtype

open Nat

namespace Nat

section Factorial

/-- `Nat.factorial n` is the factorial of `n`. -/
def factorial : ℕ → ℕ
  | 0 => 1
  | succ n => succ n * factorial n

/-- factorial notation `n!` -/
scoped notation:10000 n "!" => Nat.factorial n

theorem factorial_pos : ∀ n, 0 < n !
  | 0 => Nat.zero_lt_one
  | succ n => Nat.mul_pos (succ_pos _) (factorial_pos n)

theorem factorial_dvd_factorial {m n} (h : m ≤ n) : m ! ∣ n ! := by
  induction h with
  | refl => exact Nat.dvd_refl _
  | step _ ih => exact Nat.dvd_trans ih (Nat.dvd_mul_left _ _)

theorem dvd_factorial : ∀ {m n}, 0 < m → m ≤ n → m ∣ n !
  | succ _, _, _, h => Nat.dvd_trans (Nat.dvd_mul_right _ _) (factorial_dvd_factorial h)

end Factorial

section Infinite

/-- Euclid's theorem on the **infinitude of primes**.
Here given in the form: for every `n`, there exists a prime number `p ≥ n`. -/
theorem exists_infinite_primes (n : ℕ) : ∃ p, n ≤ p ∧ Prime p := by
  let p := minFac (n ! + 1)
  have f1 : n ! + 1 ≠ 1 := by
    apply ne_of_gt
    apply succ_lt_succ
    apply factorial_pos n
  have pp : Prime p := by
    apply minFac_prime
    apply f1
  have np : n ≤ p := by
    apply le_of_not_ge
    apply fun h =>
      have h₁ : p ∣ n ! := by
        apply dvd_factorial
        apply minFac_pos
        apply h
      have h₂ : p ∣ 1 := by
        rw [Nat.dvd_add_iff_right h₁]
        apply minFac_dvd (n ! + 1)
      -- by by_contra apply pp.not_dvd_one h₂
      pp.not_dvd_one h₂
  use p

#check exists_infinite_primes

end Infinite

end Nat
