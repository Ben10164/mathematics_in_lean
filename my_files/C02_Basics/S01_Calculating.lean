import my_files.Common

-- An example.
example (a b c : ℝ) : a * b * c = b * (a * c) := by
  rw [mul_comm a b]
  rw [mul_assoc b a c]

-- Try these.
example (a b c : ℝ) : c * b * a = b * (a * c) := by
  rw [mul_comm c b]
  rw [mul_assoc b c a]
  rw [mul_comm c a]

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  rw [mul_comm]
  rw [mul_assoc b c a]
  rw [mul_comm a c]

-- An example.
example (a b c : ℝ) : a * b * c = b * c * a := by
  rw [mul_assoc]
  rw [mul_comm]

/- Try doing the first of these without providing any arguments at all,
   and the second with only one argument. -/
example (a b c : ℝ) : a * (b * c) = b * (c * a) := by
  rw [mul_comm]
  rw [mul_assoc]

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  rw [mul_comm]
  rw [mul_assoc]
  rw [mul_comm a c]

-- Using facts from the local context.
example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h']
  rw [← mul_assoc]
  rw [h]
  rw [mul_assoc]

example (a b c d e f : ℝ) (h : b * c = e * f) : a * b * c * d = a * e * f * d := by
  rw [mul_assoc a b ]
  rw [h]
  rw [← mul_assoc]

example (a b c d : ℝ) (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 := by
  rw [hyp]
  rw [hyp']
  rw [mul_comm]
  rw [← hyp']
  rw [sub_self]


example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h', ← mul_assoc, h, mul_assoc]

section

variable (a b c d e f : ℝ)

example (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h', ← mul_assoc, h, mul_assoc]

end

section
variable (a b c : ℝ)

#check a
#check a + b
#check (a : ℝ)
#check mul_comm a b
#check (mul_comm a b : a * b = b * a)
#check mul_assoc c a b
#check mul_comm a
#check mul_comm

end

section
variable (a b : ℝ)

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  rw [mul_add, add_mul, add_mul]
  rw [← add_assoc, add_assoc (a * a)]
  rw [mul_comm b a, ← two_mul]

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
  calc
    (a + b) * (a + b) = a * a + b * a + (a * b + b * b) := by
      rw [mul_add, add_mul, add_mul]
    _ = a * a + (b * a + a * b) + b * b := by
      rw [← add_assoc, add_assoc (a * a)]
    _ = a * a + 2 * (a * b) + b * b := by
      rw [mul_comm b a, ← two_mul]

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
  calc
    (a + b) * (a + b) = a * a + b * a + (a * b + b * b) := by
      rw [mul_add, add_mul, add_mul]
    _ = a * a + (b * a + a * b) + b * b := by
      rw [← add_assoc, add_assoc (a * a)]
    _ = a * a + 2 * (a * b) + b * b := by
      rw [mul_comm b a, ← two_mul]

end

-- Try these. For the second, use the theorems listed underneath.
section
variable (a b c d : ℝ)

example : (a + b) * (c + d) = a * c + a * d + b * c + b * d := by
  rw [add_mul]
  rw [mul_add, mul_add]
  rw [← add_assoc]


example (a b : ℝ) : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  rw [pow_two, pow_two]
  rw [add_mul]
  rw [mul_sub]
  rw [mul_comm a b]
  rw [mul_sub]
  rw [add_sub, sub_add]
  rw [← mul_sub]
  rw [sub_self, mul_zero, sub_zero]


#check add_mul a b c
#check mul_add a b c
#check add_assoc a b c
#check pow_two a
#check mul_sub a b c
#check mul_comm a b
#check add_sub a b c
#check sub_add a b c
#check sub_self a
#check mul_zero a
#check sub_zero a

end

-- Examples.

section
variable (a b c d : ℝ)

example (a b c d : ℝ) (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp'] at hyp
  rw [mul_comm d a] at hyp
  rw [← two_mul (a * d)] at hyp
  rw [← mul_assoc 2 a d] at hyp
  exact hyp

example : c * b * a = b * (a * c) := by
  rw [mul_comm c b]
  rw [mul_comm a c]
  rw [mul_assoc]

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  /-
  a b c d : ℝ
  ⊢ (a + b) * (a + b) = a * a + 2 * (a * b) + b * b
  -/
  rw [mul_add]
  /-
  a b c d : ℝ
  ⊢ (a + b) * a + (a + b) * b = a * a + 2 * (a * b) + b * b
  -/
  rw [add_mul]
  /-
  a b c d : ℝ
  ⊢ a * a + b * a + (a + b) * b = a * a + 2 * (a * b) + b * b
  -/
  rw [← mul_assoc]
  /-
  a b c d : ℝ
  ⊢ a * a + b * a + (a + b) * b = a * a + 2 * a * b + b * b
  -/
  rw [add_mul]
  /-
  a b c d : ℝ
  ⊢ a * a + b * a + (a * b + b * b) = a * a + 2 * a * b + b * b
  -/
  rw [← add_assoc]
  /-
  a b c d : ℝ
  ⊢ a * a + b * a + a * b + b * b = a * a + 2 * a * b + b * b
  -/
  rw [mul_assoc]
  /-
  a b c d : ℝ
  ⊢ a * a + b * a + a * b + b * b = a * a + 2 * (a * b) + b * b
  -/
  rw [two_mul (a * b)]
  /-
  a b c d : ℝ
  ⊢ a * a + b * a + a * b + b * b = a * a + (a * b + a * b) + b * b
  -/
  rw [mul_comm b a]
  /-
  a b c d : ℝ
  ⊢ a * a + a * b + a * b + b * b = a * a + (a * b + a * b) + b * b
  -/
  rw [add_assoc (a * a) (a * b) (a * b)]
  /-
  a b c d : ℝ
  ⊢ a * a + (a * b + a * b) + b * b = a * a + (a * b + a * b) + b * b
  -/

example : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  /-
  a b c d : ℝ
  ⊢ (a + b) * (a - b) = a ^ 2 - b ^ 2
  -/
  rw [add_mul]
  /-
  a b c d : ℝ
  ⊢ a * (a - b) + b * (a - b) = a ^ 2 - b ^ 2
  -/
  rw [mul_sub,  mul_sub]
  /-
  a b c d : ℝ
  ⊢ a * a - a * b + (b * a - b * b) = a ^ 2 - b ^ 2
  -/
  rw [add_sub]
  /-
  a b c d : ℝ
  ⊢ a * a - a * b + b * a - b * b = a ^ 2 - b ^ 2
  -/
  rw [mul_comm a b]
  /-
  a b c d : ℝ
  ⊢ a * a - b * a + b * a - b * b = a ^ 2 - b ^ 2
  -/
  rw [← neg_add_eq_sub (b*a)]
  /-
  a b c d : ℝ
  ⊢ -(b * a) + a * a + b * a - b * b = a ^ 2 - b ^ 2
  -/
  rw [add_comm]
  /-
  a b c d : ℝ
  ⊢ b * a + (-(b * a) + a * a) - b * b = a ^ 2 - b ^ 2
  -/
  rw [← add_assoc]
  /-
  a b c d : ℝ
  ⊢ b * a + -(b * a) + a * a - b * b = a ^ 2 - b ^ 2
  -/
  rw [add_neg_cancel]
  /-
  a b c d : ℝ
  ⊢ 0 + a * a - b * b = a ^ 2 - b ^ 2
  -/
  rw [← pow_two, ← pow_two]
  /-
  a b c d : ℝ
  ⊢ 0 + a ^ 2 - b ^ 2 = a ^ 2 - b ^ 2
  -/
  rw [add_comm]
  /-
  a b c d : ℝ
  ⊢ a ^ 2 + 0 - b ^ 2 = a ^ 2 - b ^ 2
  -/
  rw [add_zero]
  /-
  a b c d : ℝ
  ⊢ a ^ 2 - b ^ 2 = a ^ 2 - b ^ 2
  -/

example (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  /-
  a b c d : ℝ
  hyp : c = d * a + b
  hyp' : b = a * d
  ⊢ c = 2 * a * d
  -/
  rw [hyp, hyp']
  /-
  a b c d : ℝ
  hyp : c = d * a + b
  hyp' : b = a * d
  ⊢ d * a + a * d = 2 * a * d
  -/
  rw [mul_comm d a]
  rw [← two_mul (a * d)]
  rw [mul_assoc]

end

example (a b c : ℕ) (h : a + b = c) : (a + b) * (a + b) = a * c + b * c := by
  /-
  a b c : ℕ
  h : a + b = c
  ⊢ (a + b) * (a + b) = a * c + b * c
  -/
  nth_rw 2 [h]
  /-
  a b c : ℕ
  h : a + b = c
  ⊢ (a + b) * c = a * c + b * c
  -/
  rw [add_mul]
  /-
  a b c : ℕ
  h : a + b = c
  ⊢ a * c + b * c = a * c + b * c
  -/
