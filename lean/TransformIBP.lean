import PrimeNumberTheoremAnd.IEANTN.Varlamov.ExactTransform
import PrimeNumberTheoremAnd.IEANTN.Varlamov.KernelDerivatives

namespace Varlamov.Kernel
open Real MeasureTheory

noncomputable def scaledLaplace (n : ℕ) (z : ℂ) : ℂ :=
  ∫ u in (0 : ℝ)..d, Complex.exp (-z * (u : ℂ)) * (scaledDerivative n u : ℂ)

lemma scaledDerivative_zero : scaledDerivative 0 = piece := by
  funext u
  simp [scaledDerivative, piece, unit]
lemma scaledLaplace_zero (z : ℂ) : scaledLaplace 0 z = W z := by
  simp only [scaledLaplace, scaledDerivative_zero, W]

lemma scaledLaplace_integrable (n : ℕ) (z : ℂ) :
    IntervalIntegrable
      (fun u : ℝ => Complex.exp (-z * (u : ℂ)) * (scaledDerivative n u : ℂ)) volume 0 d := by
  apply Continuous.intervalIntegrable
  dsimp [scaledDerivative]
  fun_prop

/-- One integration by parts, with endpoint terms retained exactly. -/
lemma scaledLaplace_ibp (n : ℕ) (z : ℂ) :
    z * scaledLaplace n z = (scaledDerivative n 0 : ℂ) -
      Complex.exp (-z * (d : ℂ)) * (scaledDerivative n d : ℂ) + scaledLaplace (n + 1) z := by
  have hder (u : ℝ) :
      HasDerivAt (fun v : ℝ => Complex.exp (-z * (v : ℂ)) * (scaledDerivative n v : ℂ))
        (Complex.exp (-z * (u : ℂ)) * (scaledDerivative (n + 1) u : ℂ) -
          z * (Complex.exp (-z * (u : ℂ)) * (scaledDerivative n u : ℂ))) u := by
    have hreal : HasDerivAt (fun v : ℝ => (v : ℂ)) (1 : ℂ) u :=
      (hasDerivAt_id u).ofReal_comp
    have he := (hreal.const_mul (-z)).cexp
    have hw := (scaledDerivative_hasDerivAt n u).ofReal_comp
    convert he.mul hw using 1 <;> (try dsimp) <;> ring
  have hi := (scaledLaplace_integrable (n + 1) z).sub ((scaledLaplace_integrable n z).const_mul z)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hder u) hi
  rw [intervalIntegral.integral_sub (scaledLaplace_integrable (n + 1) z)
    ((scaledLaplace_integrable n z).const_mul z), intervalIntegral.integral_const_mul] at h
  have h' : scaledLaplace (n + 1) z - z * scaledLaplace n z =
      Complex.exp (-z * (d : ℂ)) * (scaledDerivative n d : ℂ) - (scaledDerivative n 0 : ℂ) := by
    simpa only [scaledLaplace, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul] using h
  linear_combination - h'

/-- Three integrations by parts expose the cubic decay of the remainder. -/
theorem W_sub_main {z : ℂ} (hz : z ≠ 0) :
    W z - 10 / z = ((scaledDerivative 2 0 : ℂ) + scaledLaplace 3 z) / z ^ 3 := by
  have hp10 := piece_first_zero
  have hp1d := piece_first_end
  have hp2d := piece_second_end
  rw [iteratedDeriv_piece] at hp10 hp1d hp2d
  have h0 := scaledLaplace_ibp 0 z
  have h1 := scaledLaplace_ibp 1 z
  have h2 := scaledLaplace_ibp 2 z
  simp only [scaledDerivative_zero, scaledLaplace_zero, piece_at_zero, piece_at_end,
    Complex.ofReal_zero, Complex.ofReal_ofNat, mul_zero, sub_zero] at h0
  simp only [hp10, hp1d, Complex.ofReal_zero, mul_zero, zero_sub, neg_zero, zero_add] at h1
  simp only [hp2d, Complex.ofReal_zero, mul_zero, sub_zero] at h2
  field_simp
  linear_combination z ^ 2 * h0 + z * h1 + h2

lemma W_sub_main_norm {z : ℂ} (hz : z ≠ 0) :
    ‖W z - 10 / z‖ ≤ (|scaledDerivative 2 0| + ‖scaledLaplace 3 z‖) / ‖z‖ ^ 3 := by
  rw [W_sub_main hz, norm_div, norm_pow]
  apply div_le_div_of_nonneg_right _ (by positivity)
  simpa only [Complex.norm_real, Real.norm_eq_abs] using
    norm_add_le (scaledDerivative 2 0 : ℂ) (scaledLaplace 3 z)

#print axioms W_sub_main

end Varlamov.Kernel
