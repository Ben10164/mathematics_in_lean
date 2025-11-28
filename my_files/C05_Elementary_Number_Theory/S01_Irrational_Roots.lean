import my_files.Common

#print Nat.Coprime

example (m n : Nat) (h : m.Coprime n) : m.gcd n = 1 :=
  h

#eval Nat.Coprime 4 9

example (m n : Nat) (h : m.Coprime n) : m.gcd n = 1 := by
  rw [Nat.Coprime] at h
  exact h

example : Nat.Coprime 12 7 := by norm_num

example : Nat.gcd 12 8 = 4 := by norm_num

#check Nat.prime_def_lt

example (p : ℕ) (prime_p : Nat.Prime p) : 2 ≤ p ∧ ∀ m : ℕ, m < p → m ∣ p → m = 1 := by
  rwa [Nat.prime_def_lt] at prime_p

-- same as
example (p : ℕ) (prime_p : Nat.Prime p) : 2 ≤ p ∧ ∀ m : ℕ, m < p → m ∣ p → m = 1 := by
  rw [Nat.prime_def_lt] at prime_p
  apply prime_p

#check Nat.Prime.eq_one_or_self_of_dvd

example (p : ℕ) (prime_p : Nat.Prime p) : ∀ m : ℕ, m ∣ p → m = 1 ∨ m = p :=
  prime_p.eq_one_or_self_of_dvd

example : Nat.Prime 17 := by norm_num

-- my_files.Commonly used
example : Nat.Prime 2 :=
  Nat.prime_two

example : Nat.Prime 3 :=
  Nat.prime_three

#check Nat.Prime.dvd_mul
#check Nat.Prime.dvd_mul Nat.prime_two
#check Nat.prime_two.dvd_mul

theorem even_of_even_sqr {m : ℕ} (h : 2 ∣ m ^ 2) : 2 ∣ m := by
  rw [pow_two, Nat.prime_two.dvd_mul] at h
  cases h <;> assumption

example {m : ℕ} (h : 2 ∣ m ^ 2) : 2 ∣ m :=
  Nat.Prime.dvd_of_dvd_pow Nat.prime_two h

example (a b c : Nat) (h : a * b = a * c) (h' : a ≠ 0) : b = c :=
  -- apply? suggests the following:
  (mul_right_inj' h').mp h

example {m n : ℕ} (coprime_mn : m.Coprime n) : m ^ 2 ≠ 2 * n ^ 2 := by
  intro sqr_eq
  have two_dvd_m: 2 ∣ m := by
    apply even_of_even_sqr
    rw [sqr_eq]
    apply dvd_mul_right
  obtain ⟨k, meq⟩ := dvd_iff_exists_eq_mul_left.mp two_dvd_m
  have two_two_k_sq_eq_two_n_sq: 2 * (2 * k ^ 2) = 2 * n ^ 2 := by
    rw [← sqr_eq, meq]
    ring
  have two_k_sq_eq_n_sq: 2 * k ^ 2 = n ^ 2 := by
    symm
    rw [← mul_right_inj' two_ne_zero]
    rw [two_two_k_sq_eq_two_n_sq]
  have two_dvd_n: 2 ∣ n := by
    apply even_of_even_sqr
    rw [← two_k_sq_eq_n_sq]
    apply dvd_mul_of_dvd_left
    apply refl
  have two_dvd_gcd: 2 ∣ m.gcd n := by
    apply Nat.dvd_gcd
    apply two_dvd_m
    apply two_dvd_n
  have : 2 ∣ 1 := by
    convert two_dvd_gcd
    symm
    exact coprime_mn
  norm_num at this

example {m n p : ℕ} (coprime_mn : m.Coprime n) (prime_p : p.Prime) : m ^ 2 ≠ p * n ^ 2 := by
  intro sqr_eq
  have p_dvd_m : p ∣ m := by
    apply prime_p.dvd_of_dvd_pow
    rw [sqr_eq]
    apply dvd_mul_right
  obtain ⟨k, meq⟩ := dvd_iff_exists_eq_mul_left.mp p_dvd_m
  have : p * (p * k ^ 2) = p * n ^ 2 := by
    rw [← sqr_eq]
    rw [sq, sq]
    rw [meq]
    ring
    -- rw [mul_comm]
    -- nth_rw 1 [mul_comm k p]
    -- rw [← mul_assoc, ← mul_assoc]
  have : p * k ^ 2 = n ^ 2 := by
    apply (mul_right_inj' (prime_p.ne_zero)).mp
    apply this
  have p_dvd_n : p ∣ n := by
    apply prime_p.dvd_of_dvd_pow
    rw [← this]
    apply dvd_mul_right
  have : p ∣ Nat.gcd m n := by
    apply dvd_gcd
    apply p_dvd_m
    apply p_dvd_n
  have : p ∣ 1 := by
    convert this
    symm
    apply coprime_mn
  have : 2 ≤ 1 := by
    apply prime_p.two_le.trans
    apply Nat.le_of_dvd
    . norm_num
    . apply this
  norm_num at this

#check Nat.primeFactorsList
#check Nat.prime_of_mem_primeFactorsList
#check Nat.prod_primeFactorsList
#check Nat.primeFactorsList_unique

theorem factorization_mul' {m n : ℕ} (mnez : m ≠ 0) (nnez : n ≠ 0) (p : ℕ) :
    (m * n).factorization p = m.factorization p + n.factorization p := by
  rw [Nat.factorization_mul mnez nnez]
  rfl

theorem factorization_pow' (n k p : ℕ) :
    (n ^ k).factorization p = k * n.factorization p := by
  rw [Nat.factorization_pow]
  rfl

theorem Nat.Prime.factorization' {p : ℕ} (prime_p : p.Prime) :
    p.factorization p = 1 := by
  rw [prime_p.factorization]
  simp

example {m n p : ℕ} (nnz : n ≠ 0) (prime_p : p.Prime) : m ^ 2 ≠ p * n ^ 2 := by
  intro sqr_eq
  have nsqr_nez : n ^ 2 ≠ 0 := by simpa
  have eq1 : Nat.factorization (m ^ 2) p = 2 * m.factorization p := by
    rw [factorization_pow']
  have eq2 : (p * n ^ 2).factorization p = 2 * n.factorization p + 1 := by
    rw [factorization_mul']
    . rw [prime_p.factorization']
      rw [factorization_pow']
      rw [add_comm]
    . apply prime_p.ne_zero
    . apply nsqr_nez
  have : 2 * m.factorization p % 2 = (2 * n.factorization p + 1) % 2 := by
    rw [← eq1, sqr_eq, eq2]
  rw [add_comm, Nat.add_mul_mod_self_left, Nat.mul_mod_right] at this
  norm_num at this

example {m n k r : ℕ} (nnz : n ≠ 0) (pow_eq : m ^ k = r * n ^ k) {p : ℕ} :
    k ∣ r.factorization p := by
  rcases r with _ | r
  · simp
  have npow_nz : n ^ k ≠ 0 := fun npowz ↦ nnz (eq_zero_of_pow_eq_zero npowz)
  have eq1 : (m ^ k).factorization p = k * m.factorization p := by
    rw [factorization_pow']
  have eq2 : ((r + 1) * n ^ k).factorization p =
      k * n.factorization p + (r + 1).factorization p := by
    rw [factorization_mul']
    rw [factorization_pow']
    rw [add_comm]
    . apply Nat.add_one_ne_zero
    . apply npow_nz
  have : r.succ.factorization p = k * m.factorization p - k * n.factorization p := by
    rw [← eq1, pow_eq, eq2, add_comm, Nat.add_sub_cancel]
  rw [this]
  apply Nat.dvd_sub
  apply dvd_mul_right
  apply dvd_mul_right

#check multiplicity
