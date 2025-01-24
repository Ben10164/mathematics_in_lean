import MIL.Common

section RingAxioms
  variable (R : Type*) [Ring R]

  #check (add_assoc : ∀ a b c : R, a + b + c = a + (b + c))
  #check (add_comm : ∀ a b : R, a + b = b + a)
  #check (zero_add : ∀ a : R, 0 + a = a)
  #check (neg_add_cancel : ∀ a : R, -a + a = 0)
  #check (mul_assoc : ∀ a b c : R, a * b * c = a * (b * c))
  #check (mul_one : ∀ a : R, a * 1 = a)
  #check (one_mul : ∀ a : R, 1 * a = a)
  #check (mul_add : ∀ a b c : R, a * (b + c) = a * b + a * c)
  #check (add_mul : ∀ a b c : R, (a + b) * c = a * c + b * c)

end RingAxioms

section CommRing
  variable (R : Type*) [CommRing R]
  variable (a b c d : R)

  example : c * b * a = b * (a * c) := by ring

  example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by ring

  example : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by ring

  example (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
    rw [hyp, hyp']
    ring

end CommRing

namespace MyRing
  variable {R : Type*} [Ring R]

  theorem add_zero (a : R) : a + 0 = a := by rw [add_comm, zero_add]

  theorem add_right_neg (a : R) : a + -a = 0 := by rw [add_comm, neg_add_cancel]

  #check MyRing.add_zero
  #check add_zero

end MyRing

namespace MyRing
  variable {R : Type*} [Ring R]

  theorem neg_add_cancel_left (a b : R) : -a + (a + b) = b := by
    rw [← add_assoc, neg_add_cancel, zero_add]

  -- Prove these:
  theorem add_neg_cancel_right (a b : R) : a + b + -b = a := by
    rw [add_comm]
    rw [add_comm a b]
    rw [← add_assoc]
    rw [neg_add_cancel]
    rw [add_comm]
    rw [add_zero]

  theorem add_left_cancel {a b c : R} (h : a + b = a + c) : b = c := by
    rw [← neg_add_cancel_left a b]
    rw [h]
    rw [neg_add_cancel_left]

  theorem add_right_cancel {a b c : R} (h : a + b = c + b) : a = c := by
    rw [← add_neg_cancel_right a b]
    rw [h]
    rw [add_neg_cancel_right]

  theorem mul_zero (a : R) : a * 0 = 0 := by
    have h : a * 0 + a * 0 = a * 0 + 0 := by
      rw [← mul_add, add_zero, add_zero]
    rw [add_left_cancel h]

  theorem zero_mul (a : R) : 0 * a = 0 := by
    have h : 0 * a + 0 * a = 0 + 0 * a := by
      rw [← two_mul]
      rw [← mul_assoc]
      rw [add_comm, mul_zero, add_zero]
    rw [add_right_cancel h]


  theorem neg_eq_of_add_eq_zero {a b : R} (h : a + b = 0) : -a = b := by
    rw [← add_neg_cancel_right a b]
    rw [neg_add]
    rw [h]
    rw [neg_zero]
    rw [neg_neg]
    rw [zero_add]

  theorem eq_neg_of_add_eq_zero {a b : R} (h : a + b = 0) : a = -b := by
    rw [← add_neg_cancel_right a b]
    rw [h]
    rw [zero_add]

  theorem neg_zero : (-0 : R) = 0 := by
    apply neg_eq_of_add_eq_zero
    rw [add_zero]

  theorem neg_neg (a : R) : - -a = a := by
    apply neg_eq_of_add_eq_zero
    rw [add_comm]
    rw [add_neg_cancel]

end MyRing

section DifferentSolutions
  variable {R : Type*} [Ring R]

  example (a b : R) : a - b = a + -b :=
    sub_eq_add_neg a b

  example (a b : ℝ) : a - b = a + -b := by
    rw [← sub_neg_eq_add]
    rw [neg_neg]

  example (a b : ℝ) : a - b = a + -b :=
    rfl

  example (a b : ℝ) : a - b = a + -b := by
    rfl

end DifferentSolutions

namespace MyRing
  variable {R : Type*} [Ring R]

  theorem self_sub (a : R) : a - a = 0 := by
    rw [sub_eq_add_neg]
    rw [add_comm]
    rw [neg_add_cancel]


  theorem one_add_one_eq_two : 1 + 1 = (2 : R) := by
    norm_num

  theorem two_mul (a : R) : 2 * a = a + a := by
    rw [← one_add_one_eq_two]
    rw [add_mul]
    rw [one_mul]

end MyRing

section AddGroup
  variable (A : Type*) [AddGroup A]

  #check (add_assoc : ∀ a b c : A, a + b + c = a + (b + c))
  #check (zero_add : ∀ a : A, 0 + a = a)
  #check (neg_add_cancel : ∀ a : A, -a + a = 0)

end AddGroup

section GroupG
  variable {G : Type*} [Group G]

  #check (mul_assoc : ∀ a b c : G, a * b * c = a * (b * c))
  /-
  mul_assoc : ∀ (a b c : G), a * b * c = a * (b * c)
  -/
  #check (one_mul : ∀ a : G, 1 * a = a)
  /-
  one_mul : ∀ (a : G), 1 * a = a
  -/
  #check (inv_mul_cancel : ∀ a : G, a⁻¹ * a = 1)
  /-
  inv_mul_cancel : ∀ (a : G), a⁻¹ * a = 1
  -/

  namespace MyGroup
    theorem mul_inv_cancel (a : G) : a * a⁻¹ = 1 := by
    -- a * a⁻¹ = 1
      have h1 : (a * a⁻¹)⁻¹ * (a * a⁻¹ * (a * a⁻¹)) = 1 := by
        -- ⊢ (a * a⁻¹)⁻¹ * (a * a⁻¹ * (a * a⁻¹)) = 1
        rw [mul_assoc]
        -- ⊢ (a * a⁻¹)⁻¹ * (a * (a⁻¹ * (a * a⁻¹))) = 1
        rw [← mul_assoc a⁻¹ a]
        -- ⊢ (a * a⁻¹)⁻¹ * (a * (a⁻¹ * a * a⁻¹)) = 1
        rw [inv_mul_cancel a]
        -- ⊢ (a * a⁻¹)⁻¹ * (a * (1 * a⁻¹)) = 1
        rw [one_mul]
        -- ⊢ (a * a⁻¹)⁻¹ * (a * a⁻¹) = 1
        rw [inv_mul_cancel (a * a⁻¹)]
        -- ⊢ 1 = 1
      rw[← h1]
      -- ⊢ a * a⁻¹ = (a * a⁻¹)⁻¹ * (a * a⁻¹ * (a * a⁻¹))
      rw[← mul_assoc]
      -- ⊢ a * a⁻¹ = (a * a⁻¹)⁻¹ * (a * a⁻¹) * (a * a⁻¹)
      rw[inv_mul_cancel (a * a⁻¹)]
      -- ⊢ a * a⁻¹ = 1 * (a * a⁻¹)
      rw [one_mul]
      -- a * a⁻¹ = a * a⁻¹

    theorem mul_one (a : G) : a * 1 = a := by
    -- ⊢ a * 1 = a
      rw [← inv_mul_cancel a]
      -- ⊢ a * (a⁻¹ * a) = a
      rw [← mul_assoc]
      -- ⊢ a * a⁻¹ * a = a
      rw [mul_inv_cancel]
      -- ⊢ 1 * a = a
      rw [one_mul]
      -- ⊢ a = a

    theorem mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
    -- ⊢ (a * b)⁻¹ = b⁻¹ * a⁻¹
      rw[← one_mul (b⁻¹ * a⁻¹)]
      -- ⊢ ......... = 1 * (b⁻¹ * a⁻¹)
      rw [← inv_mul_cancel (a*b)]
      -- ⊢ ......... = (a * b)⁻¹ * (a * b) * (b⁻¹ * a⁻¹)
      rw[← mul_assoc]
      -- ⊢ ......... = (a * b)⁻¹ * (a * b) * b⁻¹ * a⁻¹
      rw [← mul_assoc (a * b)⁻¹]
      -- ⊢ ......... = (a * b)⁻¹ * a * b * b⁻¹ * a⁻¹
      rw [mul_assoc]
      -- ⊢ ......... = (a * b)⁻¹ * a * b * (b⁻¹ * a⁻¹)
      rw [mul_assoc]
      -- ⊢ ......... = (a * b)⁻¹ * a * (b * (b⁻¹ * a⁻¹))
      rw [← mul_assoc b]
      -- ⊢ ......... = (a * b)⁻¹ * a * (b * b⁻¹ * a⁻¹)
      rw[mul_inv_cancel b]
      -- ⊢ ......... = (a * b)⁻¹ * a * (1 * a⁻¹)
      rw [one_mul]
      -- ⊢ ......... = (a * b)⁻¹ * a * a⁻¹
      rw [mul_assoc]
      -- ⊢ ......... = (a * b)⁻¹ * (a * a⁻¹)
      rw[mul_inv_cancel]
      -- ⊢ ......... = (a * b)⁻¹ * 1
      rw [mul_one]
      -- ⊢ ......... = (a * b)⁻¹

  end MyGroup

end GroupG
