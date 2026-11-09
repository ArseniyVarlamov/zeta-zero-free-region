import PrimeNumberTheoremAnd.IEANTN.Varlamov.TransformIBP
import Mathlib.Analysis.Complex.Trigonometric

namespace Varlamov.Kernel
open Real MeasureTheory

noncomputable def C (ν : ℝ) : ℝ := |scaledDerivative 2 0| +
  scaledDerivative 3 0 * (1 + exp (-ν * d)) / ν + M4star / ν ^ 2
noncomputable def Cminus : ℝ := |scaledDerivative 2 0| +
  d * exp d * (scaledDerivative 3 0 + M4star * d)

lemma scaled_third_pos : 0 < scaledDerivative 3 0 := by
  simpa only [iteratedDeriv_piece] using piece_third_zero_pos

lemma norm_integrand (n : ℕ) (z : ℂ) (u : ℝ) :
    ‖Complex.exp (-z * (u : ℂ)) * (scaledDerivative n u : ℂ)‖ =
      exp (-z.re * u) * |scaledDerivative n u| := by
  simp only [norm_mul, Complex.norm_exp, Complex.mul_re, Complex.neg_re,
    Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    Complex.norm_real, Real.norm_eq_abs]

lemma integral_exp_neg_le {ν : ℝ} (hν : 0 < ν) :
    (∫ u in (0 : ℝ)..d, exp (-ν * u)) ≤ 1 / ν := by
  have hn : -ν ≠ 0 := ne_of_lt (neg_neg_of_pos hν)
  rw [intervalIntegral.integral_comp_mul_left _ hn, integral_exp]
  simp only [mul_zero, exp_zero, smul_eq_mul]
  have he := exp_nonneg (-(ν * d))
  apply (le_div_iff₀ hν).mpr
  field_simp
  nlinarith

lemma scaledLaplace_norm_exp {n : ℕ} {z : ℂ} {ν K : ℝ}
    (hν : 0 < ν) (hz : ν ≤ z.re) (hK0 : 0 ≤ K)
    (hK : ∀ u ∈ Set.Icc (0 : ℝ) d, |scaledDerivative n u| ≤ K) :
    ‖scaledLaplace n z‖ ≤ K / ν := by
  have hbound : ∀ᵐ u : ℝ, u ∈ Set.Ioc (0 : ℝ) d →
      ‖Complex.exp (-z * (u : ℂ)) * (scaledDerivative n u : ℂ)‖ ≤ K * exp (-ν * u) := by
    apply Filter.Eventually.of_forall
    intro u hu
    rw [norm_integrand]
    have he : exp (-z.re * u) ≤ exp (-ν * u) :=
      exp_le_exp.mpr (by nlinarith [hu.1])
    calc
      _ ≤ exp (-z.re * u) * K := mul_le_mul_of_nonneg_left (hK u ⟨hu.1.le, hu.2⟩) (exp_nonneg _)
      _ ≤ K * exp (-ν * u) := by nlinarith
  have hi : IntervalIntegrable (fun u : ℝ => K * exp (-ν * u)) volume 0 d := by
    apply Continuous.intervalIntegrable
    fun_prop
  have h := intervalIntegral.norm_integral_le_of_norm_le d_pos.le hbound hi
  rw [intervalIntegral.integral_const_mul] at h
  calc
    ‖scaledLaplace n z‖ ≤ K * (∫ u in (0 : ℝ)..d, exp (-ν * u)) := h
    _ ≤ K * (1 / ν) := mul_le_mul_of_nonneg_left (integral_exp_neg_le hν) hK0
    _ = K / ν := by ring

lemma scaledLaplace_norm_const {n : ℕ} {z : ℂ} {K : ℝ}
    (hz : -1 ≤ z.re) (hK0 : 0 ≤ K)
    (hK : ∀ u ∈ Set.Icc (0 : ℝ) d, |scaledDerivative n u| ≤ K) :
    ‖scaledLaplace n z‖ ≤ d * exp d * K := by
  have hbound : ∀ u ∈ Set.uIoc (0 : ℝ) d,
      ‖Complex.exp (-z * (u : ℂ)) * (scaledDerivative n u : ℂ)‖ ≤ exp d * K := by
    intro u hu
    rw [Set.uIoc_of_le d_pos.le] at hu
    rw [norm_integrand]
    have he : exp (-z.re * u) ≤ exp d := exp_le_exp.mpr (by nlinarith [hu.1, hu.2])
    calc
      _ ≤ exp (-z.re * u) * K := mul_le_mul_of_nonneg_left (hK u ⟨hu.1.le, hu.2⟩) (exp_nonneg _)
      _ ≤ exp d * K := mul_le_mul_of_nonneg_right he hK0
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  simpa only [scaledLaplace, sub_zero, abs_of_pos d_pos, mul_assoc, mul_comm,
    mul_left_comm] using h

lemma scaledLaplace_three_formula {z : ℂ} (hz : z ≠ 0) :
    scaledLaplace 3 z = ((scaledDerivative 3 0 : ℂ) *
      (1 + Complex.exp (-z * (d : ℂ))) + scaledLaplace 4 z) / z := by
  have hp := piece_third_endpoints
  rw [iteratedDeriv_piece] at hp
  have h := scaledLaplace_ibp 3 z
  rw [hp, Complex.ofReal_neg, mul_neg, sub_neg_eq_add] at h
  simp only [neg_mul] at h ⊢
  field_simp
  linear_combination h

lemma scaledLaplace_three_norm {z : ℂ} {ν : ℝ} (hν : 0 < ν) (hz : ν ≤ z.re) :
    ‖scaledLaplace 3 z‖ ≤
      (scaledDerivative 3 0 * (1 + exp (-ν * d)) + M4star / ν) / ν := by
  have hnorm : ν ≤ ‖z‖ := hz.trans ((le_abs_self z.re).trans (Complex.abs_re_le_norm z))
  have hz0 : z ≠ 0 := norm_pos_iff.mp (hν.trans_le hnorm)
  have hexp : ‖Complex.exp (-z * (d : ℂ))‖ ≤ exp (-ν * d) := by
    rw [Complex.norm_exp]
    simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero]
    exact exp_le_exp.mpr (by nlinarith [d_pos])
  have hL4 : ‖scaledLaplace 4 z‖ ≤ M4star / ν :=
    scaledLaplace_norm_exp hν hz M4star_pos.le (fun u hu => by
      simpa only [iteratedDeriv_piece] using fourth_derivative_bound hu)
  have hp : ‖(scaledDerivative 3 0 : ℂ) * (1 + Complex.exp (-z * (d : ℂ)))‖ ≤
      scaledDerivative 3 0 * (1 + exp (-ν * d)) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos scaled_third_pos]
    apply mul_le_mul_of_nonneg_left _ scaled_third_pos.le
    exact (norm_add_le 1 _).trans (by simp only [norm_one]; linarith [hexp])
  rw [scaledLaplace_three_formula hz0, norm_div]
  have hnum : ‖(scaledDerivative 3 0 : ℂ) * (1 + Complex.exp (-z * (d : ℂ))) + scaledLaplace 4 z‖ ≤
      scaledDerivative 3 0 * (1 + exp (-ν * d)) + M4star / ν :=
    (norm_add_le _ _).trans (add_le_add hp hL4)
  calc
    _ ≤ (scaledDerivative 3 0 * (1 + exp (-ν * d)) + M4star / ν) / ‖z‖ :=
      div_le_div_of_nonneg_right hnum (norm_nonneg z)
    _ ≤ _ := div_le_div_of_nonneg_left
      (add_nonneg (mul_nonneg scaled_third_pos.le (by positivity))
        (div_nonneg M4star_pos.le hν.le)) hν hnorm

@[blueprint "varlamov-transform-right-bound"
  (title := "Varlamov, Lemma 4.2: right-half-plane transform bound")
  (statement := /-- If $\Re z\ge\nu>0$, then
  $|W(z)-10/z|\le C(\nu)/|z|^3$, with exactly the constant used in the article. -/)
  (uses := ["varlamov-fourth-derivative-bound", "varlamov-exact-transform"])]
theorem W_right_bound {z : ℂ} {ν : ℝ} (hν : 0 < ν) (hz : ν ≤ z.re) :
    ‖W z - 10 / z‖ ≤ C ν / ‖z‖ ^ 3 := by
  have hnorm : ν ≤ ‖z‖ := hz.trans ((le_abs_self z.re).trans (Complex.abs_re_le_norm z))
  have hz0 : z ≠ 0 := norm_pos_iff.mp (hν.trans_le hnorm)
  apply (W_sub_main_norm hz0).trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  unfold C
  have h := scaledLaplace_three_norm hν hz
  have he : (scaledDerivative 3 0 * (1 + exp (-ν * d)) + M4star / ν) / ν =
      scaledDerivative 3 0 * (1 + exp (-ν * d)) / ν + M4star / ν ^ 2 := by ring
  rw [he] at h
  linarith

@[blueprint "varlamov-transform-left-bound"
  (title := "Varlamov, Lemma 4.2: enlarged-half-plane transform bound")
  (statement := /-- If $\Re z\ge-1$ and $z\ne0$, then
  $|W(z)-10/z|\le C_{-}/|z|^3$. -/)
  (uses := ["varlamov-fourth-derivative-bound", "varlamov-exact-transform"])]
theorem W_left_bound {z : ℂ} (hz0 : z ≠ 0) (hz : -1 ≤ z.re) :
    ‖W z - 10 / z‖ ≤ Cminus / ‖z‖ ^ 3 := by
  have hK0 : 0 ≤ scaledDerivative 3 0 + M4star * d :=
    add_nonneg scaled_third_pos.le (mul_nonneg M4star_pos.le d_pos.le)
  have hL3 : ‖scaledLaplace 3 z‖ ≤ d * exp d * (scaledDerivative 3 0 + M4star * d) :=
    scaledLaplace_norm_const hz hK0 (fun u hu => by
      simpa only [iteratedDeriv_piece] using third_derivative_bound hu)
  apply (W_sub_main_norm hz0).trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  unfold Cminus
  exact add_le_add le_rfl hL3

#print axioms W_right_bound
#print axioms W_left_bound

end Varlamov.Kernel
