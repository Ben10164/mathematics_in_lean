import MIL.Common

namespace C06S01
noncomputable section

@[ext]
structure Point where
  x : ℝ
  y : ℝ
  z : ℝ

#check Point.ext

example (a b : Point) (hx : a.x = b.x) (hy : a.y = b.y) (hz : a.z = b.z) : a = b := by
  ext
  repeat' assumption

def myPoint1 : Point where
  x := 2
  y := -1
  z := 4

def myPoint2 : Point :=
  ⟨2, -1, 4⟩

def myPoint3 :=
  Point.mk 2 (-1) 4

structure Point' where build ::
  x : ℝ
  y : ℝ
  z : ℝ

#check Point'.build 2 (-1) 4

namespace Point

def add (a b : Point) : Point :=
  ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩

def add' (a b : Point) : Point where
  x := a.x + b.x
  y := a.y + b.y
  z := a.z + b.z

#check add myPoint1 myPoint2
#eval (add myPoint1 myPoint2).x
#check myPoint1.add myPoint2

end Point

#check Point.add myPoint1 myPoint2
#check myPoint1.add myPoint2

namespace Point

protected theorem add_comm (a b : Point) : add a b = add b a := by
  rw [add, add]
  ext <;> dsimp
  repeat' apply add_comm

example (a b : Point) : add a b = add b a := by simp [add, add_comm]

theorem add_x (a b : Point) : (a.add b).x = a.x + b.x :=
  rfl

def addAlt : Point → Point → Point
  | Point.mk x₁ y₁ z₁, Point.mk x₂ y₂ z₂ => ⟨x₁ + x₂, y₁ + y₂, z₁ + z₂⟩

def addAlt' : Point → Point → Point
  | ⟨x₁, y₁, z₁⟩, ⟨x₂, y₂, z₂⟩ => ⟨x₁ + x₂, y₁ + y₂, z₁ + z₂⟩

theorem addAlt_x (a b : Point) : (a.addAlt b).x = a.x + b.x := by
  rfl

theorem addAlt_comm (a b : Point) : addAlt a b = addAlt b a := by
  rw [addAlt, addAlt]
  -- the same proof still works, but the goal view here is harder to read
  ext <;> dsimp
  repeat' apply add_comm

protected theorem add_assoc (a b c : Point) : (a.add b).add c = a.add (b.add c) := by
  rw [add]
  rw [add]
  rw [add]
  rw [add]
  simp
  constructor
  . rw [← add_assoc]
  . constructor
    . rw [← add_assoc]
    . rw [← add_assoc]

def smul (r : ℝ) (a : Point) : Point :=
  ⟨a.x * r, a.y * r, a.z * r⟩

theorem smul_distrib (r : ℝ) (a b : Point) : (smul r a).add (smul r b) = smul r (a.add b) := by
  rw[smul]
  rw[smul]
  rw[smul]
  rw [add]
  rw [add]
  simp
  constructor
  . rw [← add_mul]
  . constructor
    . rw [← add_mul]
    . rw [← add_mul]

end Point



structure StandardTwoSimplex where
  x : ℝ
  y : ℝ
  z : ℝ
  x_nonneg : 0 ≤ x
  y_nonneg : 0 ≤ y
  z_nonneg : 0 ≤ z
  sum_eq : x + y + z = 1

namespace StandardTwoSimplex

def swapXy (a : StandardTwoSimplex) : StandardTwoSimplex
    where
  x := a.y
  y := a.x
  z := a.z
  x_nonneg := a.y_nonneg
  y_nonneg := a.x_nonneg
  z_nonneg := a.z_nonneg
  sum_eq := by rw [add_comm a.y a.x, a.sum_eq]

noncomputable section

def midpoint (a b : StandardTwoSimplex) : StandardTwoSimplex
    where
  x := (a.x + b.x) / 2
  y := (a.y + b.y) / 2
  z := (a.z + b.z) / 2
  x_nonneg := by
    apply div_nonneg
    . apply add_nonneg
      . apply a.x_nonneg
      . apply b.x_nonneg
    . apply zero_le_two
  y_nonneg :=  by
    apply div_nonneg
    . apply add_nonneg
      . apply a.y_nonneg
      . apply b.y_nonneg
    . apply zero_le_two
  z_nonneg := by
    apply div_nonneg
    . apply add_nonneg
      . apply a.z_nonneg
      . apply b.z_nonneg
    . apply zero_le_two
  sum_eq := by
    field_simp
    rw [← add_assoc]
    rw [← add_assoc]
    rw [add_assoc a.x b.x a.y]
    rw [add_comm b.x a.y]
    rw [← add_assoc]
    rw [add_assoc (a.x + a.y + b.x)]
    rw [add_comm b.y a.z]
    rw [← add_assoc]
    rw [add_assoc (a.x + a.y)]
    rw [add_comm b.x a.z]
    rw [← add_assoc]
    rw [a.sum_eq]
    rw [add_assoc]
    rw [add_assoc]
    rw [add_comm]
    rw [← add_assoc]
    rw [b.sum_eq]
    apply one_add_one_eq_two

def weightedAverage (lambda : Real) (lambda_nonneg : 0 ≤ lambda) (lambda_le : lambda ≤ 1)
    (a b : StandardTwoSimplex) : StandardTwoSimplex where
  x := lambda * a.x + (1 - lambda) * b.x
  y := lambda * a.y + (1 - lambda) * b.y
  z := lambda * a.z + (1 - lambda) * b.z
  x_nonneg := by
    apply add_nonneg
    . apply mul_nonneg
      . apply lambda_nonneg
      . apply a.x_nonneg
    . apply mul_nonneg
      . apply sub_nonneg_of_le
        apply lambda_le
      . apply b.x_nonneg
  y_nonneg := by
    apply add_nonneg
    . apply mul_nonneg
      . apply lambda_nonneg
      . apply a.y_nonneg
    . apply mul_nonneg
      . apply sub_nonneg_of_le
        apply lambda_le
      . apply b.y_nonneg
  z_nonneg := by
    apply add_nonneg
    . apply mul_nonneg
      . apply lambda_nonneg
      . apply a.z_nonneg
    . apply mul_nonneg
      . apply sub_nonneg_of_le
        apply lambda_le
      . apply b.z_nonneg
  sum_eq := by
    -- first line taken from the solution... :(
    trans (a.x + a.y + a.z) * lambda + (b.x + b.y + b.z) * (1 - lambda)
    -- how trans works:
    -- we have : a = c
    -- trans b
    -- now we prove a = b, and b = c
    . rw [sum_eq]
      rw [sum_eq]
      rw [one_mul]
      rw [one_mul]
      rw [add_sub_cancel]
      rw [← add_assoc]
      rw [← add_assoc]
      rw [add_assoc (lambda * a.x) ((1-lambda) * b.x)]
      rw [add_comm ((1-lambda) * b.x)]
      rw [← add_assoc]
      rw [add_assoc (lambda * a.x + lambda * a.y + (1 - lambda) * b.x)]
      rw [add_comm ((1-lambda) * b.y)]
      rw [← add_assoc]
      rw [add_assoc (lambda * a.x + lambda * a.y)]
      rw [add_comm ((1 - lambda) * b.x)]
      rw [← add_assoc]
      rw [← mul_add]
      rw [← mul_add]
      rw [sum_eq]
      rw [add_assoc (lambda * 1)]
      rw [← mul_add]
      rw [add_assoc (lambda * 1)]
      rw [← mul_add]
      rw [sum_eq]
      rw [mul_one]
      rw [mul_one]
      rw [add_sub_cancel]
    . rw [sum_eq]
      rw [sum_eq]
      rw [one_mul]
      rw [one_mul]
      rw [add_sub_cancel]

end

end StandardTwoSimplex

open BigOperators

structure StandardSimplex (n : ℕ) where
  V : Fin n → ℝ
  NonNeg : ∀ i : Fin n, 0 ≤ V i
  sum_eq_one : (∑ i, V i) = 1

namespace StandardSimplex

def midpoint (n : ℕ) (a b : StandardSimplex n) : StandardSimplex n
    where
  V i := (a.V i + b.V i) / 2
  NonNeg := by
    intro i
    apply div_nonneg
    · linarith [a.NonNeg i, b.NonNeg i]
    norm_num
  sum_eq_one := by
    simp [div_eq_mul_inv, ← Finset.sum_mul, Finset.sum_add_distrib,
      a.sum_eq_one, b.sum_eq_one]
    field_simp

def weightedAverage {n : ℕ} (lambda : Real) (lambda_nonneg : 0 ≤ lambda) (lambda_le : lambda ≤ 1)
    (a b : StandardSimplex n) : StandardSimplex n
    where
    V i := lambda * a.V i + (1 - lambda) * b.V i
    NonNeg i := by
      apply add_nonneg
      . apply mul_nonneg
        . apply lambda_nonneg
        . apply a.NonNeg
      . apply mul_nonneg
        . apply sub_nonneg_of_le
          . apply lambda_le
        . apply b.NonNeg
    sum_eq_one := by
      trans (lambda * ∑ i, a.V i) + (1 - lambda) * ∑ i, b.V i
      . rw [Finset.sum_add_distrib]
        rw [Finset.mul_sum]
        rw [Finset.mul_sum]
      . rw [sum_eq_one]
        rw [sum_eq_one]
        rw [mul_one]
        rw [mul_one]
        rw [add_sub_cancel]

end StandardSimplex

structure IsLinear (f : ℝ → ℝ) where
  is_additive : ∀ x y, f (x + y) = f x + f y
  preserves_mul : ∀ x c, f (c * x) = c * f x

section
variable (f : ℝ → ℝ) (linf : IsLinear f)

#check linf.is_additive
#check linf.preserves_mul

end

def Point'' :=
  ℝ × ℝ × ℝ

def IsLinear' (f : ℝ → ℝ) :=
  (∀ x y, f (x + y) = f x + f y) ∧ ∀ x c, f (c * x) = c * f x

def PReal :=
  { y : ℝ // 0 < y }

section
variable (x : PReal)

#check x.val
#check x.property
#check x.1
#check x.2

end

def StandardTwoSimplex' :=
  { p : ℝ × ℝ × ℝ // 0 ≤ p.1 ∧ 0 ≤ p.2.1 ∧ 0 ≤ p.2.2 ∧ p.1 + p.2.1 + p.2.2 = 1 }

def StandardSimplex' (n : ℕ) :=
  { v : Fin n → ℝ // (∀ i : Fin n, 0 ≤ v i) ∧ (∑ i, v i) = 1 }

def StdSimplex := Σ n : ℕ, StandardSimplex n

section
variable (s : StdSimplex)

#check s.fst
#check s.snd

#check s.1
#check s.2

end
