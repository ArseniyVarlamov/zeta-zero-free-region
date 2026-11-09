import PrimeNumberTheoremAnd.IEANTN.Varlamov.GammaRationalProjection
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

namespace Varlamov.Kernel
open Real Complex MeasureTheory

lemma W0_scaled_norm {η δ : ℝ} {u : ℂ} (hη : 0 < η) (hδ : 0 < δ) (hu : δ ≤ u.re) :
    ‖W0 (u / (η : ℂ))‖ ≤ C (δ / η) * η ^ 3 / ‖u‖ ^ 3 := by
  have h := W_right_bound (div_pos hδ hη)
    (show δ / η ≤ (u / (η : ℂ)).re by rw [Complex.div_ofReal_re]; exact div_le_div_of_nonneg_right hu hη.le)
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hη] at h
  change ‖W (u / (η : ℂ)) - 10 / (u / (η : ℂ))‖ ≤ _
  convert h using 1
  rw [div_pow, div_div_eq_mul_div]

lemma continuous_lineWeight {η : ℝ} {s : ℂ} (hη : 0 < η) (hs : (1 / 2 : ℝ) < s.re) :
    Continuous (lineWeight η s) := by
  let φ : ℝ → ℂ := fun y => (s - gammaLine y) / (η : ℂ)
  have hφ : Continuous φ := by dsimp [φ, gammaLine]; fun_prop
  have hn : ∀ y : ℝ, φ y ≠ 0 := by
    intro y h
    have hre : 0 < (φ y).re := by
      simp only [φ, gammaLine, Complex.div_ofReal_re, Complex.sub_re,
        Complex.add_re, Complex.ofReal_re, Complex.mul_I_re, Complex.ofReal_im,
        add_zero, sub_zero]
      exact div_pos (by linarith) hη
    rw [h] at hre
    simpa using hre
  change Continuous (fun y => W (φ y) - 10 / φ y)
  exact (differentiable_W.continuous.comp hφ).sub (continuous_const.div hφ hn)

lemma integrable_cauchy_shift {δ τ : ℝ} (hδ : 0 < δ) :
    Integrable (fun y : ℝ => 1 / (δ ^ 2 + (y - τ) ^ 2)) := by
  have h0 := integrable_inv_one_add_sq.comp_mul_left' (inv_ne_zero (ne_of_gt hδ))
  have h1 := h0.comp_add_right (-τ)
  have h2 := h1.const_mul (1 / δ ^ 2)
  convert h2 using 1
  funext y
  have hden : δ ^ 2 + (y - τ) ^ 2 ≠ 0 := ne_of_gt (by positivity)
  field_simp
  ring

/-- The cubic transform decay is sufficient for a linear-in-height gamma
approximation error to be integrable on the full contour. No Cauchy input is used. -/
theorem weighted_line_integrable {η : ℝ} {s : ℂ} (hη : 0 < η) (hs : (1 / 2 : ℝ) < s.re) :
    Integrable (fun y : ℝ => (1 + |y|) * ‖lineWeight η s y‖) := by
  let δ : ℝ := s.re - 1 / 2
  let τ : ℝ := s.im
  let P : ℝ := C (δ / η) * η ^ 3
  let k : ℝ := 1 + |τ|
  let D : ℝ := P * (k / δ + 1)
  have hδ : 0 < δ := sub_pos.mpr hs
  have hP : 0 < P := mul_pos (C_pos (div_pos hδ hη)) (pow_pos hη 3)
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have hbound (y : ℝ) : (1 + |y|) * ‖lineWeight η s y‖ ≤ D / (δ ^ 2 + (y - τ) ^ 2) := by
    let U : ℂ := s - gammaLine y
    let r : ℝ := ‖U‖
    have hUre : U.re = δ := by simp [U, gammaLine, δ]
    have hδr : δ ≤ r := by rw [← hUre]; exact Complex.re_le_norm U
    have hr : 0 < r := hδ.trans_le hδr
    have hrne : r ≠ 0 := ne_of_gt hr
    have hν := W0_scaled_norm hη hδ (show δ ≤ U.re by rw [hUre])
    have hV : ‖lineWeight η s y‖ ≤ P / r ^ 3 := hν
    have hUim : U.im = τ - y := by simp [U, gammaLine, τ]
    have hDiff : |y - τ| ≤ r := by
      have h := Complex.abs_im_le_norm U
      rw [hUim, abs_sub_comm] at h
      exact h
    have hy : |y| ≤ |τ| + r := by
      calc
        |y| = |τ + (y - τ)| := by congr 1; ring
        _ ≤ |τ| + |y - τ| := abs_add_le _ _
        _ ≤ |τ| + r := add_le_add le_rfl hDiff
    have hsq : r ^ 2 = δ ^ 2 + (y - τ) ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hUre, hUim]
      ring
    calc
      _ ≤ (k + r) * (P / r ^ 3) := mul_le_mul (by dsimp [k]; linarith) hV (norm_nonneg _) (by positivity)
      _ = P * (k / r + 1) / r ^ 2 := by field_simp 
      _ ≤ P * (k / δ + 1) / r ^ 2 := by gcongr
      _ = _ := by rw [hsq]
  have hdom : Integrable (fun y : ℝ => D / (δ ^ 2 + (y - τ) ^ 2)) := by
    simpa only [mul_one_div] using (integrable_cauchy_shift (τ := τ) hδ).const_mul D
  have hc : Continuous (fun y : ℝ => (1 + |y|) * ‖lineWeight η s y‖) :=
    (continuous_const.add continuous_abs).mul (continuous_lineWeight hη hs).norm
  apply hdom.mono' hc.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro y
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) (norm_nonneg _))]
  exact hbound y

#print axioms weighted_line_integrable

end Varlamov.Kernel
