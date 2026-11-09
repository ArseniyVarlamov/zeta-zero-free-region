import PrimeNumberTheoremAnd.IEANTN.Varlamov.GammaRationalProjection
import PrimeNumberTheoremAnd.IEANTN.Varlamov.DigammaBounds

namespace Varlamov.Kernel
open Real Complex MeasureTheory Filter Topology
open scoped BigOperators

noncomputable def digammaPartial (z : ℂ) (N : ℕ) : ℂ :=
  (∑ n ∈ Finset.range N, digammaSummand z n) - (Real.eulerMascheroniConstant : ℂ)
noncomputable def Psi (z : ℂ) : ℂ := (Complex.digamma (z / 2) + Complex.digamma ((1 - z) / 2)) / 2

lemma gammaRational_average (n : ℕ) (z : ℂ) :
    gammaRational n z = (digammaSummand (z / 2) n + digammaSummand ((1 - z) / 2) n) / 2 := by
  have h1 : z / 2 + (n : ℂ) = (z + 2 * (n : ℂ)) / 2 := by ring
  have h2 : (1 - z) / 2 + (n : ℂ) = (1 - z + 2 * (n : ℂ)) / 2 := by ring
  unfold digammaSummand gammaRational
  rw [h1, h2, inv_div, inv_div]
  ring

lemma psiPartial_average (N : ℕ) (z : ℂ) :
    psiPartial N z = (digammaPartial (z / 2) N + digammaPartial ((1 - z) / 2) N) / 2 := by
  induction N with
  | zero => simp only [psiPartial, digammaPartial, Finset.sum_range_zero, zero_sub]; ring
  | succ N ih =>
      rw [psiPartial, ih, gammaRational_average]
      simp only [digammaPartial, Finset.sum_range_succ]
      ring

lemma digammaPartial_tendsto {z : ℂ} (hz : 0 < z.re) :
    Tendsto (fun N : ℕ => digammaPartial z N) atTop (𝓝 (Complex.digamma z)) := by
  have hs := digamma_hasSum hz (le_refl z.re)
  simpa [digammaPartial] using hs.tendsto_sum_nat.sub_const (Real.eulerMascheroniConstant : ℂ)

lemma psiPartial_line_tendsto (y : ℝ) :
    Tendsto (fun N : ℕ => psiPartial N (gammaLine y)) atTop (𝓝 (Psi (gammaLine y))) := by
  have h1 : 0 < (gammaLine y / 2).re := by norm_num [gammaLine, Complex.div_re, Complex.normSq_apply]
  have h2 : 0 < ((1 - gammaLine y) / 2).re := by norm_num [gammaLine, Complex.div_re, Complex.normSq_apply]
  simp_rw [psiPartial_average]
  exact ((digammaPartial_tendsto h1).add (digammaPartial_tendsto h2)).div_const (2 : ℂ)

lemma digammaPartial_error {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) {z : ℂ}
    (hz : a ≤ z.re) {N : ℕ} (hN : 1 ≤ N) :
    ‖Complex.digamma z - digammaPartial z N‖ ≤ (‖z‖ + 1) / (a * (N : ℝ)) := by
  have he : Complex.digamma z - digammaPartial z N =
      Complex.digamma z + Real.eulerMascheroniConstant - (∑ n ∈ Finset.range N, digammaSummand z n) := by
    unfold digammaPartial
    ring
  rw [he]
  exact digamma_partial_error ha ha1 hz hN

/-- A uniform, linear-in-height dominator for the finite gamma approximations. -/
theorem psiPartial_line_error (y : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    ‖Psi (gammaLine y) - psiPartial N (gammaLine y)‖ ≤ 12 * (1 + |y|) / (N : ℝ) := by
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have h1 : (1 / 4 : ℝ) ≤ (gammaLine y / 2).re := by norm_num [gammaLine, Complex.div_re, Complex.normSq_apply]
  have h2 : (1 / 4 : ℝ) ≤ ((1 - gammaLine y) / 2).re := by norm_num [gammaLine, Complex.div_re, Complex.normSq_apply]
  have hE1 := digammaPartial_error (a := (1 / 4 : ℝ)) (by norm_num) (by norm_num) h1 hN
  have hE2 := digammaPartial_error (a := (1 / 4 : ℝ)) (by norm_num) (by norm_num) h2 hN
  have hLine : ‖gammaLine y‖ ≤ (1 / 2 : ℝ) + |y| := by
    apply (norm_add_le _ _).trans_eq
    norm_num [gammaLine, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hnorm1 : ‖gammaLine y / 2‖ ≤ |y| + 1 := by
    calc
      _ = ‖gammaLine y‖ / 2 := by rw [norm_div]; norm_num
      _ ≤ ((1 / 2 : ℝ) + |y|) / 2 := div_le_div_of_nonneg_right hLine (by norm_num)
      _ ≤ _ := by linarith [abs_nonneg y]
  have hnorm2 : ‖(1 - gammaLine y) / 2‖ ≤ |y| + 1 := by
    have hn := norm_sub_le (1 : ℂ) (gammaLine y)
    norm_num only [norm_one] at hn
    calc
      _ = ‖1 - gammaLine y‖ / 2 := by rw [norm_div]; norm_num
      _ ≤ (1 + ‖gammaLine y‖) / 2 := div_le_div_of_nonneg_right hn (by norm_num)
      _ ≤ _ := by linarith [abs_nonneg y]
  have hdom : 0 < (1 / 4 : ℝ) * (N : ℝ) := by positivity
  have he1 : ‖Complex.digamma (gammaLine y / 2) - digammaPartial (gammaLine y / 2) N‖ ≤
      (|y| + 2) / ((1 / 4 : ℝ) * (N : ℝ)) := hE1.trans
        (div_le_div_of_nonneg_right (by linarith) hdom.le)
  have he2 : ‖Complex.digamma ((1 - gammaLine y) / 2) - digammaPartial ((1 - gammaLine y) / 2) N‖ ≤
      (|y| + 2) / ((1 / 4 : ℝ) * (N : ℝ)) := hE2.trans
        (div_le_div_of_nonneg_right (by linarith) hdom.le)
  have heq : Psi (gammaLine y) - psiPartial N (gammaLine y) =
      ((Complex.digamma (gammaLine y / 2) - digammaPartial (gammaLine y / 2) N) +
        (Complex.digamma ((1 - gammaLine y) / 2) - digammaPartial ((1 - gammaLine y) / 2) N)) / 2 := by
    rw [psiPartial_average]
    unfold Psi
    ring
  rw [heq, norm_div, show ‖(2 : ℂ)‖ = (2 : ℝ) from by norm_num]
  calc
    _ ≤ (‖Complex.digamma (gammaLine y / 2) - digammaPartial (gammaLine y / 2) N‖ +
        ‖Complex.digamma ((1 - gammaLine y) / 2) - digammaPartial ((1 - gammaLine y) / 2) N‖) / 2 :=
      div_le_div_of_nonneg_right (norm_add_le _ _) (by norm_num)
    _ ≤ ((|y| + 2) / ((1 / 4 : ℝ) * (N : ℝ)) + (|y| + 2) / ((1 / 4 : ℝ) * (N : ℝ))) / 2 :=
      div_le_div_of_nonneg_right (add_le_add he1 he2) (by norm_num)
    _ = 4 * (|y| + 2) / (N : ℝ) := by ring
    _ ≤ _ := div_le_div_of_nonneg_right (by linarith [abs_nonneg y]) hNp.le

#print axioms psiPartial_line_tendsto
#print axioms psiPartial_line_error

end Varlamov.Kernel
