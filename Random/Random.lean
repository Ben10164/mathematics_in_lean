import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Defs

open Bool Subtype

open Nat

namespace Nat

section Infinite

/-- Euclid's theorem on the **infinitude of primes**.
Here given in the form: for every `n`, there exists a prime number `p ≥ n`. -/
theorem exists_infinite_primes (n : ℕ) : ∃ p, n ≤ p ∧ Prime p :=
  let p := minFac (n ! + 1)
  have f1 : n ! + 1 ≠ 1 := by
    apply ne_of_gt
    apply succ_lt_succ
    apply factorial_pos
  have pp : Prime p := by
    apply minFac_prime
    apply f1
  have np : n ≤ p :=
    le_of_not_ge fun h =>
      have h₁ : p ∣ n ! := by
        apply dvd_factorial
        apply minFac_pos
        apply h
      have h₂ : p ∣ 1 := by
        apply (Nat.dvd_add_iff_right h₁).2
        apply minFac_dvd
      pp.not_dvd_one h₂

  ⟨p, np, pp⟩

end Infinite

end Nat
