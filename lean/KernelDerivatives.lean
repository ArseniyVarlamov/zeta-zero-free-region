import PrimeNumberTheoremAnd.IEANTN.Varlamov.Kernel
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

namespace Varlamov.Kernel
open Real Polynomial

noncomputable def scaledDerivative (n : ℕ) (u : ℝ) : ℝ :=
  ((Polynomial.derivative^[n]) unitPoly).eval (u / d) / d ^ n

lemma scaledDerivative_hasDerivAt (n : ℕ) (u : ℝ) :
    HasDerivAt (scaledDerivative n) (scaledDerivative (n + 1) u) u := by
  have hp := (((Polynomial.derivative^[n]) unitPoly).hasDerivAt (u / d)).comp u
    ((hasDerivAt_id u).div_const d)
  have h := hp.div_const (d ^ n)
  have hd : d ≠ 0 := ne_of_gt d_pos
  convert h using 1
  · rfl
  · unfold scaledDerivative
    rw [Function.iterate_succ_apply', pow_succ]
    field_simp

lemma iteratedDeriv_piece (n : ℕ) : iteratedDeriv n piece = scaledDerivative n := by
  induction n with
  | zero => funext u; simp [scaledDerivative, piece, unit]
  | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      funext u
      exact (scaledDerivative_hasDerivAt n u).deriv

noncomputable def unitD3 (x : ℝ) : ℝ :=
  ((1949476490131772700 / 8116714872719329)) +
    ((4739689932378327360 / 8116714872719329)) * x ^ 1 +
    ((-13612335316263545400 / 8116714872719329)) * x ^ 2 +
    ((5441697346108363200 / 8116714872719329)) * x ^ 4 +
    ((-468004942486690560 / 8116714872719329)) * x ^ 6

lemma unitD3_eval (x : ℝ) : ((Polynomial.derivative^[3]) unitPoly).eval x = unitD3 x := by
  norm_num [unitPoly, unitD3, Function.iterate_succ_apply', Polynomial.derivative_pow]
  ring

noncomputable def unitD4 (x : ℝ) : ℝ :=
  ((4739689932378327360 / 8116714872719329)) +
    ((-27224670632527090800 / 8116714872719329)) * x ^ 1 +
    ((21766789384433452800 / 8116714872719329)) * x ^ 3 +
    ((-2808029654920143360 / 8116714872719329)) * x ^ 5

lemma unitD4_eval (x : ℝ) : ((Polynomial.derivative^[4]) unitPoly).eval x = unitD4 x := by
  norm_num [unitPoly, unitD4, Function.iterate_succ_apply', Polynomial.derivative_pow]
  ring

noncomputable def unitM4 : ℝ := 7990027925264043120 / 8116714872719329
noncomputable def M4star : ℝ := unitM4 / d ^ 4

lemma unitM4_pos : 0 < unitM4 := by norm_num [unitM4]
lemma M4star_pos : 0 < M4star := div_pos unitM4_pos (pow_pos d_pos 4)

lemma unitD4_lower : ∀ x ∈ Set.Icc (0 : ℝ) 1, -unitM4 ≤ unitD4 x := by
  unfold unitD4 unitM4
  bernstein_bound (trust := kernel)
lemma unitD4_upper : ∀ x ∈ Set.Icc (0 : ℝ) 1, unitD4 x ≤ unitM4 := by
  unfold unitD4 unitM4
  bernstein_bound (trust := kernel)
lemma unitD3_lower : ∀ x ∈ Set.Icc (0 : ℝ) 1, -(unitD3 0 + unitM4) ≤ unitD3 x := by
  have h0 : unitD3 0 + unitM4 = (9939504415395815820 / 8116714872719329 : ℝ) := by
    norm_num [unitD3, unitM4]
  rw [h0]
  unfold unitD3
  bernstein_bound (trust := kernel)
lemma unitD3_upper : ∀ x ∈ Set.Icc (0 : ℝ) 1, unitD3 x ≤ unitD3 0 + unitM4 := by
  have h0 : unitD3 0 + unitM4 = (9939504415395815820 / 8116714872719329 : ℝ) := by
    norm_num [unitD3, unitM4]
  rw [h0]
  unfold unitD3
  bernstein_bound (trust := kernel)

lemma normalized_mem {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) d) : u / d ∈ Set.Icc (0 : ℝ) 1 := by
  exact ⟨div_nonneg hu.1 d_pos.le, (div_le_one d_pos).mpr hu.2⟩

@[blueprint "varlamov-fourth-derivative-bound"
  (title := "Varlamov, Lemma 4.1(5): fourth derivative")
  (statement := /-- The fourth derivative of the polynomial piece satisfies
  $|w^{(4)}(u)|\le w_4^*$ on $[0,d]$, with the exact rational Bernstein bound
  used by the certificate. -/)]
theorem fourth_derivative_bound {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) d) :
    |iteratedDeriv 4 piece u| ≤ M4star := by
  rw [iteratedDeriv_piece]
  unfold scaledDerivative M4star
  rw [unitD4_eval, abs_div, abs_of_pos (pow_pos d_pos 4)]
  exact div_le_div_of_nonneg_right
    (abs_le.mpr ⟨unitD4_lower _ (normalized_mem hu), unitD4_upper _ (normalized_mem hu)⟩)
    (pow_nonneg d_pos.le 4)

lemma third_derivative_bound {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) d) :
    |iteratedDeriv 3 piece u| ≤ iteratedDeriv 3 piece 0 + M4star * d := by
  rw [iteratedDeriv_piece]
  unfold scaledDerivative
  rw [unitD3_eval, unitD3_eval, abs_div, abs_of_pos (pow_pos d_pos 3)]
  have h := div_le_div_of_nonneg_right
    (abs_le.mpr ⟨unitD3_lower _ (normalized_mem hu), unitD3_upper _ (normalized_mem hu)⟩)
    (pow_nonneg d_pos.le 3)
  have hd : d ≠ 0 := ne_of_gt d_pos
  convert h using 1
  unfold M4star
  simp only [zero_div]
  field_simp

lemma piece_at_zero : piece 0 = 10 := by simp [piece, unit_zero]
lemma piece_first_zero : iteratedDeriv 1 piece 0 = 0 := by
  rw [iteratedDeriv_piece]
  norm_num [scaledDerivative, unitPoly, Function.iterate_succ_apply', Polynomial.derivative_pow]
lemma piece_at_end : piece d = 0 := by simp [piece, ne_of_gt d_pos, unit_one]
lemma piece_first_end : iteratedDeriv 1 piece d = 0 := by
  rw [iteratedDeriv_piece]
  norm_num [scaledDerivative, unitPoly, ne_of_gt d_pos, Function.iterate_succ_apply', Polynomial.derivative_pow]
lemma piece_second_end : iteratedDeriv 2 piece d = 0 := by
  rw [iteratedDeriv_piece]
  norm_num [scaledDerivative, unitPoly, ne_of_gt d_pos, Function.iterate_succ_apply', Polynomial.derivative_pow]
lemma piece_second_zero_neg : iteratedDeriv 2 piece 0 < 0 := by
  rw [iteratedDeriv_piece]
  have hd : 0 < d ^ 2 := pow_pos d_pos 2
  apply div_neg_of_neg_of_pos _ hd
  norm_num [scaledDerivative, unitPoly, Function.iterate_succ_apply', Polynomial.derivative_pow]
lemma piece_third_zero_pos : 0 < iteratedDeriv 3 piece 0 := by
  rw [iteratedDeriv_piece]
  unfold scaledDerivative
  rw [unitD3_eval]
  exact div_pos (by norm_num [unitD3]) (pow_pos d_pos 3)
lemma piece_third_endpoints : iteratedDeriv 3 piece d = -iteratedDeriv 3 piece 0 := by
  rw [iteratedDeriv_piece]
  norm_num [scaledDerivative, unitPoly, ne_of_gt d_pos, Function.iterate_succ_apply', Polynomial.derivative_pow]
  ring

#print axioms fourth_derivative_bound
#print axioms third_derivative_bound

end Varlamov.Kernel
