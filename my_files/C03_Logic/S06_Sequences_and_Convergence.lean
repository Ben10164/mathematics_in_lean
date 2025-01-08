import MIL.Common

namespace C03S06

def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, -- for all ε > 0,
  ∃ N, -- there exists an N such that
  ∀ n ≥ N, -- for all n ≥ N,
  |s n - a| < ε -- |s(n) - a| < ε
  -- This proves that function s converges to value a

example : (fun x y : ℝ ↦ (x + y) ^ 2) = fun x y : ℝ ↦ x ^ 2 + 2 * x * y + y ^ 2 := by
  ext
  ring

example (a b : ℝ) : |a| = |a - b + b| := by
  congr
  ring

example {a : ℝ} (h : 1 < a) : a < a * a := by
  convert (mul_lt_mul_right _).2 h
  · rw [one_mul]
  exact lt_trans zero_lt_one h

theorem convergesTo_const (a : ℝ) : ConvergesTo (fun x : ℕ ↦ a) a := by
  -- ConvergesTo defines ε and εpos. we can use intro to get it into a better format for us
  intro ε εpos
  -- now its: ∃ N, ∀ n ≥ N, |(fun x => a) n - a| < ε
  -- (in addition to a ε : ℝ and εpos : ε > 0)
  use 0
  -- ∀ n ≥ 0, |(fun x => a) n - a| < ε
  intro n nge
  -- just to clarify, (fun x => a) n is a, since the function is for any x, returns a
  -- lets show this by simplifying this
  dsimp
  rw [sub_self]
  rw [abs_zero]
  apply εpos

theorem convergesTo_add {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
        ConvergesTo (fun n ↦ s n + t n) (a + b) := by
  -- We are proving that if the sequence s converges to a, and the sequence t converges to b,
  -- then the sequence defined by s n + t n converges to a + b.
  intro ε εpos
  -- Introduce ε > 0 and assume εpos: ε > 0.
  dsimp -- This line simplifies the goal, making it easier to work with.

  -- We need to find a positive number δ such that for all n ≥ δ,
  -- the absolute difference |(s n + t n) - (a + b)| is less than ε.

  -- Lets find a way to split this problem into two parts
  have ε2pos : 0 < ε / 2 := by
    linarith
  -- Since ε > 0, ε / 2 is also positive. This will be useful for splitting the problem.

  -- By the definition of convergence, there exists an Ns such that for all n ≥ Ns,
  -- the absolute difference |s n - a| is less than ε / 2.
  rcases cs (ε / 2) ε2pos with ⟨Ns, hs⟩

  -- Similarly, there exists an Nt such that for all n ≥ Nt,
  -- the absolute difference |t n - b| is less than ε / 2.
  rcases ct (ε / 2) ε2pos with ⟨Nt, ht⟩

  -- Lets choose δ to be the maximum of Ns and Nt. This ensures that n is large enough
  -- for both sequences s and t to be close to their respective limits.
  use max Ns Nt

  -- Assume n ≥ max Ns Nt.
  intro n hn

  -- Since n ≥ max Ns Nt, it follows that n ≥ Ns.
  have ngeNs : n ≥ Ns := by
    apply le_of_max_le_left hn

  -- Same thing for n ≥ Nt.
  have ngeNt : n ≥ Nt := by
    apply le_of_max_le_right hn

  calc
    -- Lets rewrite |s n + t n - (a + b)| as |s n - a + (t n - b)| using algebraic manipulation.
    |s n + t n - (a + b)| = |s n - a + (t n - b)| := by
      congr
      ring

    -- By the triangle inequality, |s n - a + (t n - b)| is less than or equal to |s n - a| + |t n - b|.
    _ ≤ |s n - a| + |t n - b| := by
      apply abs_add

    -- Since |s n - a| < ε / 2 and |t n - b| < ε / 2 for n ≥ Ns and n ≥ Nt respectively,
    -- it follows that |s n - a| + |t n - b| < ε / 2 + ε / 2.
    _ < ε / 2 + ε / 2 := by
      apply add_lt_add
      . apply hs
        apply ngeNs
      . apply ht
        apply ngeNt

    -- Finally, ε / 2 + ε / 2 simplifies to ε.
    _ = ε := by
      norm_num

theorem convergesTo_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (cs : ConvergesTo s a) :
    ConvergesTo (fun n ↦ c * s n) (c * a) := by
  by_cases h : c = 0
  · convert convergesTo_const 0
    · rw [h]
      ring
    rw [h]
    ring
  have acpos : 0 < |c| := abs_pos.mpr h
  intro ε εpos
  dsimp
  have εcpos : 0 < ε / |c| := by apply div_pos εpos acpos
  rcases cs (ε / |c|) εcpos with ⟨Ns, hs⟩
  use Ns
  intro n ngt

  calc
    |c * s n - c * a| = |c| * |s n - a| := by
      rw [← abs_mul]
      rw [mul_sub]
    _ < |c| * (ε / |c|) := by
      apply mul_lt_mul_of_pos_left
      apply hs
      apply ngt
      apply acpos
    _ = ε := by
      rw [mul_div]
      apply mul_div_cancel_left₀
      apply abs_ne_zero.mpr
      apply h

theorem exists_abs_le_of_convergesTo {s : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) :
    ∃ N b, ∀ n, N ≤ n → |s n| < b := by
  rcases cs 1 zero_lt_one with ⟨N, h⟩
  use N, |a| + 1
  intro n ngt
  calc
    |s n| = |s n - a + a| := by
      apply abs_eq_abs.mpr
      rw [sub_add_cancel]
      left
      apply rfl
    _ ≤ |s n - a| + |a| := by
      apply abs_add
    _ < |a| + 1 := by
      linarith [h n ngt]

theorem aux {s t : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) (ct : ConvergesTo t 0) :
    ConvergesTo (fun n ↦ s n * t n) 0 := by
  intro ε εpos
  dsimp
  rcases exists_abs_le_of_convergesTo cs with ⟨N₀, B, h₀⟩
  have Bpos : 0 < B := lt_of_le_of_lt (abs_nonneg _) (h₀ N₀ (le_refl _))
  have pos₀ : ε / B > 0 := div_pos εpos Bpos
  rcases ct _ pos₀ with ⟨N₁, h₁⟩
  use max N₀ N₁
  intro n ngt
  have ngeN₀ : n ≥ N₀ := by
    apply le_of_max_le_left ngt
  have ngeN₁ : n ≥ N₁ := by
    apply le_of_max_le_right ngt
  calc
    |s n * t n - 0| = |s n| * |t n - 0| := by
      rw [sub_zero]
      rw [abs_mul]
      rw [sub_zero]
    _ < B * (ε / B) := by
      apply mul_lt_mul''
      . apply h₀ n
        apply ngeN₀
      . apply h₁ n
        apply ngeN₁
      . apply abs_nonneg
      . apply abs_nonneg
    _ = ε := mul_div_cancel₀ _ (ne_of_lt Bpos).symm

theorem convergesTo_mul {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n * t n) (a * b) := by
  have h₁ : ConvergesTo (fun n ↦ s n * (t n + -b)) 0 := by
    apply aux cs
    convert convergesTo_add ct (convergesTo_const (-b))
    ring
  have := convergesTo_add h₁ (convergesTo_mul_const b cs)
  convert convergesTo_add h₁ (convergesTo_mul_const b cs) using 1
  · ext; ring
  ring

theorem convergesTo_unique {s : ℕ → ℝ} {a b : ℝ}
      (sa : ConvergesTo s a) (sb : ConvergesTo s b) :
    a = b := by
  by_contra abne
  have : |a - b| > 0 := by
    apply abs_sub_pos.mpr
    apply abne
  let ε := |a - b| / 2
  have εpos : ε > 0 := by
    change |a - b| / 2 > 0
    linarith
  rcases sa ε εpos with ⟨Na, hNa⟩
  rcases sb ε εpos with ⟨Nb, hNb⟩
  let N := max Na Nb
  have absa : |s N - a| < ε := by
    apply hNa
    apply le_max_left Na Nb
  have absb : |s N - b| < ε := by
    apply hNb
    apply le_max_right Na Nb
  have : |a - b| < |a - b|
  calc
    |a - b| = |(-(s N - a)) + (s N - b)| := by
      congr
      ring
    _ ≤ |(-(s N - a))| + |s N - b| := by
      apply abs_add
    _ = |s N - a| + |s N - b| := by
      rw [abs_neg]
    _ < ε + ε := by
      apply add_lt_add
      apply absa
      apply absb
    _ = |a - b| := by
      apply add_halves |a - b|
  apply lt_irrefl _ this

section
variable {α : Type*} [LinearOrder α]

def ConvergesTo' (s : α → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

end
