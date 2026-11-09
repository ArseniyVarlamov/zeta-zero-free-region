import PrimeNumberTheoremAnd.IEANTN.Varlamov.CauchyInput
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

namespace Varlamov
open Real MeasureTheory Filter Topology Set

lemma UpperCauchyAdmissible.continuous_real {f : ℂ → ℂ} (hf : UpperCauchyAdmissible f) :
    Continuous (fun t : ℝ => f (t : ℂ)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  exact ((hf.analytic (t : ℂ) (by simp)).continuousAt).comp
    Complex.continuous_ofReal.continuousAt

lemma UpperCauchyAdmissible.real_lorentz_bound {f : ℂ → ℂ} (hf : UpperCauchyAdmissible f) :
    ∃ D : ℝ, 0 < D ∧ ∀ t : ℝ, (1 + t ^ 2) * ‖f (t : ℂ)‖ ≤ D := by
  obtain ⟨M,hM,hdec⟩ := hf.decay
  have hc := hf.continuous_real
  have hb : BddAbove ((fun t : ℝ => ‖f (t : ℂ)‖) '' Set.Icc (-1 : ℝ) 1) :=
    isCompact_Icc.bddAbove_image hc.norm.continuousOn
  obtain ⟨K,hK⟩ := hb
  have hK0 : 0 ≤ K := (norm_nonneg (f 0)).trans
    (hK (show ‖f 0‖ ∈ (fun t : ℝ => ‖f (t : ℂ)‖) '' Set.Icc (-1 : ℝ) 1 from
      ⟨0,by norm_num,by simp⟩))
  refine ⟨2 * (M + K + 1), by positivity, ?_⟩
  intro t
  by_cases ht : |t| ≤ 1
  · have hft : ‖f (t : ℂ)‖ ≤ K := hK ⟨t,abs_le.mp ht,rfl⟩
    have ht2 : t ^ 2 ≤ 1 := by
      have hlo := (abs_le.mp ht).1
      have hhi := (abs_le.mp ht).2
      have hprod := mul_nonneg (sub_nonneg.mpr hhi) (show 0 ≤ 1 + t by linarith)
      nlinarith only [hprod]
    have hp := mul_le_mul_of_nonneg_right (show 1 + t ^ 2 ≤ 2 by linarith) (norm_nonneg (f (t : ℂ)))
    nlinarith only [hp,hft,hM,hK0]
  · have hraw := hdec (t : ℂ) (by simp)
    simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs] at hraw
    have ht2 : 1 ≤ t ^ 2 := by
      have ha : 1 ≤ |t| := (lt_of_not_ge ht).le
      have hprod := mul_nonneg (sub_nonneg.mpr ha) (show 0 ≤ |t| + 1 by positivity)
      nlinarith only [hprod, sq_abs t]
    have hp := mul_le_mul_of_nonneg_right ht2 (norm_nonneg (f (t : ℂ)))
    nlinarith only [hp,hraw,hM,hK0]

lemma cauchy_real_denominator {p : ℂ} (hp : p.im ≠ 0) (t : ℝ) :
    |p.im| ≤ ‖(t : ℂ) - p‖ ∧ (t : ℂ) - p ≠ 0 := by
  have h := Complex.abs_im_le_norm ((t : ℂ) - p)
  simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, abs_neg] at h
  refine ⟨h, ?_⟩
  intro he
  rw [he, norm_zero] at h
  exact (abs_pos.mpr hp).not_ge h

/-- The integrability clause of the classical upper-half-plane Cauchy
formula follows from the stated analytic and quadratic-decay hypotheses. -/
theorem UpperCauchyAdmissible.cauchy_line_integrable {f : ℂ → ℂ}
    (hf : UpperCauchyAdmissible f) {p : ℂ} (hp : p.im ≠ 0) :
    Integrable (fun t : ℝ => f (t : ℂ) / ((t : ℂ) - p)) := by
  obtain ⟨D,hD,hbound⟩ := hf.real_lorentz_bound
  have hI : 0 < |p.im| := abs_pos.mpr hp
  have hc : Continuous (fun t : ℝ => f (t : ℂ) / ((t : ℂ) - p)) :=
    hf.continuous_real.div (Complex.continuous_ofReal.sub continuous_const)
      (fun t => (cauchy_real_denominator hp t).2)
  have hd : Integrable (fun t : ℝ => (D / |p.im|) * (1 + t ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul _
  apply hd.mono' hc.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro t
  have hpos : (0 : ℝ) < 1 + t ^ 2 := by positivity
  have hft : ‖f (t : ℂ)‖ ≤ D / (1 + t ^ 2) := (le_div_iff₀ hpos).mpr (by nlinarith [hbound t])
  rw [norm_div]
  calc
    _ ≤ ‖f (t : ℂ)‖ / |p.im| := div_le_div_of_nonneg_left (norm_nonneg _) hI (cauchy_real_denominator hp t).1
    _ ≤ (D / (1 + t ^ 2)) / |p.im| := div_le_div_of_nonneg_right hft hI.le
    _ = _ := by ring

lemma far_resolvent_bound {f : ℂ → ℂ} {M R : ℝ} {p z : ℂ}
    (hdec : ∀ z : ℂ, 0 ≤ z.im → ‖z‖ ^ 2 * ‖f z‖ < M)
    (hR : 0 < R) (hRp : 2 * ‖p‖ ≤ R) (hz : 0 ≤ z.im) (hn : R ≤ ‖z‖) :
    ‖f z / (z - p)‖ ≤ 2 * M / R ^ 3 := by
  have hraw := hdec z hz
  have hsq : R ^ 2 ≤ ‖z‖ ^ 2 := by gcongr
  have hprod := mul_le_mul_of_nonneg_right hsq (norm_nonneg (f z))
  have hft : ‖f z‖ ≤ M / R ^ 2 := (le_div_iff₀ (sq_pos_of_pos hR)).mpr (by nlinarith only [hprod,hraw])
  have hden : R / 2 ≤ ‖z - p‖ := by nlinarith [norm_sub_norm_le z p]
  have hhalf : 0 < R / 2 := by linarith
  rw [norm_div]
  calc
    _ ≤ ‖f z‖ / (R / 2) := div_le_div_of_nonneg_left (norm_nonneg _) hhalf hden
    _ ≤ (M / R ^ 2) / (R / 2) := div_le_div_of_nonneg_right hft hhalf.le
    _ = _ := by field_simp

lemma tendsto_const_div_square (C : ℝ) :
    Tendsto (fun R : ℝ => C / R ^ 2) atTop (𝓝 0) := by
  have h := (tendsto_const_nhds : Tendsto (fun _ : ℝ => C) atTop (𝓝 C)).mul ((tendsto_inv_atTop_zero :
    Tendsto (fun R : ℝ => R⁻¹) atTop (𝓝 0)).pow 2)
  simpa only [zero_pow (by norm_num : 2 ≠ 0), mul_zero, div_eq_mul_inv, inv_pow] using h

#print axioms UpperCauchyAdmissible.cauchy_line_integrable
end Varlamov
