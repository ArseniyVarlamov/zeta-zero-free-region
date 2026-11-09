import PrimeNumberTheoremAnd.IEANTN.Varlamov.Trigonometric

/-!
Executable integer polynomials for small exact certificates. Their numerical
generators are untrusted: each certificate is checked by kernel reduction.
-/

namespace Varlamov.IntegerPolynomial
open scoped BigOperators

def add : List ℤ → List ℤ → List ℤ
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys => (x + y) :: add xs ys

def scale (a : ℤ) (xs : List ℤ) : List ℤ := xs.map (a * ·)

def mul : List ℤ → List ℤ → List ℤ
  | [], _ => []
  | x :: xs, ys => add (scale x ys) (0 :: mul xs ys)

def monomial (a : ℤ) (n : ℕ) : List ℤ := List.replicate n 0 ++ [a]

def sumRange : ℕ → (ℕ → List ℤ) → List ℤ
  | 0, _ => []
  | n + 1, f => add (sumRange n f) (f n)

def absSum (xs : List ℤ) : ℤ := (xs.map (fun a => |a|)).sum

noncomputable def eval (z : ℂ) : List ℤ → ℂ
  | [] => 0
  | x :: xs => (x : ℂ) + z * eval z xs

lemma eval_add (z : ℂ) (xs ys : List ℤ) :
    eval z (add xs ys) = eval z xs + eval z ys := by
  induction xs generalizing ys with
  | nil => simp [add, eval]
  | cons x xs ih =>
    cases ys with
    | nil => simp [add, eval]
    | cons y ys => simp only [add, eval, Int.cast_add, ih]; ring

lemma eval_sumRange (z : ℂ) (n : ℕ) (f : ℕ → List ℤ) :
    eval z (sumRange n f) = ∑ i ∈ Finset.range n, eval z (f i) := by
  induction n with
  | zero => simp [sumRange, eval]
  | succ n ih => rw [sumRange, eval_add, ih, Finset.sum_range_succ]

lemma eval_scale (z : ℂ) (a : ℤ) (xs : List ℤ) :
    eval z (scale a xs) = (a : ℂ) * eval z xs := by
  induction xs with
  | nil => simp [scale, eval]
  | cons x xs ih => simp only [scale, List.map_cons, eval, Int.cast_mul] at *; rw [ih]; ring

lemma eval_mul (z : ℂ) (xs ys : List ℤ) :
    eval z (mul xs ys) = eval z xs * eval z ys := by
  induction xs with
  | nil => simp [mul, eval]
  | cons x xs ih => rw [mul, eval_add, eval_scale, eval, eval, ih]; push_cast; ring

lemma eval_append (z : ℂ) (xs ys : List ℤ) :
    eval z (xs ++ ys) = eval z xs + z ^ xs.length * eval z ys := by
  induction xs with
  | nil => simp [eval]
  | cons x xs ih => simp only [List.cons_append, eval, ih, List.length_cons, pow_succ]; ring

lemma eval_replicate_zero (z : ℂ) (n : ℕ) : eval z (List.replicate n 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, eval, ih]

lemma eval_monomial (z : ℂ) (a : ℤ) (n : ℕ) :
    eval z (monomial a n) = (a : ℂ) * z ^ n := by
  simp [monomial, eval_append, eval_replicate_zero, eval, mul_comm]

lemma eval_conj (z : ℂ) (xs : List ℤ) :
    eval (starRingEnd ℂ z) xs = starRingEnd ℂ (eval z xs) := by
  induction xs with
  | nil => simp [eval]
  | cons x xs ih => simp [eval, ih]

lemma eval_reverse {z : ℂ} (hz : z * starRingEnd ℂ z = 1) (xs : List ℤ)
    (hn : xs ≠ []) :
    eval z xs.reverse = z ^ (xs.length - 1) * starRingEnd ℂ (eval z xs) := by
  induction xs with
  | nil => exact (hn rfl).elim
  | cons x xs ih =>
    cases xs with
    | nil => simp [eval]
    | cons y ys =>
      have ih' := ih (by simp)
      rw [List.reverse_cons, eval_append, ih']
      simp only [List.length_reverse, List.length_cons, Nat.add_sub_cancel, eval, mul_zero, add_zero,
        map_add, map_mul, map_intCast]
      have hp : z ^ (ys.length + 1) * starRingEnd ℂ z = z ^ ys.length := by
        rw [pow_succ, mul_assoc, hz, mul_one]
      conv_rhs => rw [mul_add, ← mul_assoc, hp]
      ring

lemma centered_square_nonneg {z : ℂ} (hz : z * starRingEnd ℂ z = 1)
    (xs : List ℤ) (hn : xs ≠ []) :
    0 ≤ ((z ^ (xs.length - 1))⁻¹ * eval z (mul xs xs.reverse)).re := by
  rw [eval_mul, eval_reverse hz xs hn]
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  rw [show (z ^ (xs.length - 1))⁻¹ *
      (eval z xs * (z ^ (xs.length - 1) * starRingEnd ℂ (eval z xs))) =
      eval z xs * starRingEnd ℂ (eval z xs) from by field_simp]
  simpa [Complex.mul_conj] using Complex.normSq_nonneg (eval z xs)

lemma eval_norm_le {z : ℂ} (hz : ‖z‖ ≤ 1) (xs : List ℤ) :
    ‖eval z xs‖ ≤ (xs.map (fun a => |a|)).sum := by
  induction xs with
  | nil => simp [eval]
  | cons x xs ih =>
    simp only [eval, List.map_cons, List.sum_cons, Int.cast_add]
    calc
      _ ≤ ‖(x : ℂ)‖ + ‖z * eval z xs‖ := norm_add_le _ _
      _ ≤ |(x : ℝ)| + 1 * ((xs.map (fun a => |a|)).sum : ℝ) := by
        rw [norm_mul, Complex.norm_intCast]
        gcongr
      _ = _ := by push_cast; ring

#print axioms centered_square_nonneg
end Varlamov.IntegerPolynomial
