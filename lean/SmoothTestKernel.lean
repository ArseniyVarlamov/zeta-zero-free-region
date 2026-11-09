import PrimeNumberTheoremAnd.IEANTN.Varlamov.TestKernelLaplace
import PrimeNumberTheoremAnd.IEANTN.Varlamov.CauchyInput

namespace Varlamov.Kernel
open Real MeasureTheory Topology

/-- A smooth extension to the negative half-line; all Laplace integrals and
prime samples only use nonnegative arguments, where this is exactly g_eta. -/
noncomputable def smoothDerivative (n : ℕ) (η u : ℝ) : ℝ :=
  η ^ (n + 1) * cut (scaledDerivative n) (η * u)
noncomputable def smoothKernel (η : ℝ) : ℝ → ℝ := smoothDerivative 0 η

lemma smoothDerivative_hasDerivAt (n : ℕ) (η u : ℝ)
    (hn : scaledDerivative n d = 0) (hn1 : scaledDerivative (n + 1) d = 0) :
    HasDerivAt (smoothDerivative n η) (smoothDerivative (n + 1) η u) u := by
  have hc := cut_hasDerivAt hn hn1 (scaledDerivative_hasDerivAt n) (η * u)
  have hd := ((hc.comp u (hasDerivAt_const_mul η)).const_mul (η ^ (n + 1)))
  convert hd using 1
  · rfl
  · dsimp [smoothDerivative]
    ring

lemma smoothKernel_deriv (η : ℝ) : deriv (smoothKernel η) = smoothDerivative 1 η := by
  have h0 : scaledDerivative 0 d = 0 := by rw [scaledDerivative_zero]; exact piece_at_end
  have h1 := piece_first_end
  rw [iteratedDeriv_piece] at h1
  exact funext (fun u => (smoothDerivative_hasDerivAt 0 η u h0 h1).deriv)

lemma smoothKernel_second (η : ℝ) : deriv (deriv (smoothKernel η)) = smoothDerivative 2 η := by
  rw [smoothKernel_deriv]
  have h1 := piece_first_end
  have h2 := piece_second_end
  rw [iteratedDeriv_piece] at h1 h2
  exact funext (fun u => (smoothDerivative_hasDerivAt 1 η u h1 h2).deriv)

lemma smoothKernel_contDiff (η : ℝ) : ContDiff ℝ 2 (smoothKernel η) := by
  have hc : ContDiff ℝ 2 (fun u : ℝ => η * cut piece (η * u)) :=
    contDiff_const.mul (contDiff_cut_piece.comp (by fun_prop))
  unfold smoothKernel smoothDerivative
  rw [scaledDerivative_zero]
  simpa only [zero_add, pow_one] using hc

lemma smoothKernel_eq_g {η u : ℝ} (hη : 0 < η) (hu : 0 ≤ u) : smoothKernel η u = g η u := by
  simpa only [smoothKernel, smoothDerivative, zero_add, pow_one, scaledDerivative_zero] using
    (g_eq_smooth hη hu).symm

lemma smoothDerivative_zero_of_gt (n : ℕ) {η u : ℝ} (hη : 0 < η) (hu : d / η < u) :
    smoothDerivative n η u = 0 := by
  have hηu : d < η * u := by have := (div_lt_iff₀ hη).mp hu; nlinarith
  simp only [smoothDerivative, cut_of_gt hηu, mul_zero]

lemma laplace_eq_interval_of_zero {f : ℝ → ℝ} {D : ℝ} (hD : 0 ≤ D)
    (hz : ∀ u : ℝ, D < u → f u = 0) (z : ℂ) :
    laplace f z = ∫ u in (0 : ℝ)..D, Complex.exp (-z * (u : ℂ)) * (f u : ℂ) := by
  let fplus : ℝ → ℝ := fun u => if 0 ≤ u then f u else 0
  have hs : Function.support fplus ⊆ Set.Icc (0 : ℝ) D := by
    intro u hu
    have hn : fplus u ≠ 0 := hu
    by_cases hu0 : 0 ≤ u
    · refine ⟨hu0, ?_⟩
      by_contra h
      exact hn (by simp [fplus, hu0, hz u (lt_of_not_ge h)])
    · exact False.elim (hn (by simp [fplus, hu0]))
  calc
    laplace f z = laplace fplus z := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      change 0 < u at hu
      simp only [fplus, ite_eq_left hu.le]
    _ = _ := laplace_eq_compact_interval hD hs z
    _ = _ := by
      apply intervalIntegral.integral_congr_Ioo_of_le hD
      intro u hu
      simp only [fplus, ite_eq_left hu.1.le]

lemma laplace_smoothDerivative (n : ℕ) {η : ℝ} (hη : 0 < η) (z : ℂ) :
    laplace (smoothDerivative n η) z = (η : ℂ) ^ n * scaledLaplace n (z / (η : ℂ)) := by
  let φ : ℝ → ℂ := fun v => Complex.exp (-(z / (η : ℂ)) * (v : ℂ)) * (scaledDerivative n v : ℂ)
  have hη0 : η ≠ 0 := ne_of_gt hη
  have hηC : (η : ℂ) ≠ 0 := by exact_mod_cast hη0
  have hpoint (u : ℝ) : φ (η * u) = Complex.exp (-z * (u : ℂ)) * (scaledDerivative n (η * u) : ℂ) := by
    dsimp [φ]
    push_cast
    congr 2
    field_simp
  have hchange := intervalIntegral.smul_integral_comp_mul_left φ (a := 0) (b := d / η) η
  have hend : η * (d / η) = d := by field_simp
  simp only [mul_zero, hend, Complex.real_smul] at hchange
  simp_rw [hpoint] at hchange
  rw [laplace_eq_interval_of_zero (div_nonneg d_pos.le hη.le)
    (fun u hu => smoothDerivative_zero_of_gt n hη hu) z]
  calc
    _ = ∫ u in (0 : ℝ)..(d / η), (η : ℂ) ^ (n + 1) *
        (Complex.exp (-z * (u : ℂ)) * (scaledDerivative n (η * u) : ℂ)) := by
      apply intervalIntegral.integral_congr_Ioo_of_le (div_nonneg d_pos.le hη.le)
      intro u hu
      have hηu : η * u ≤ d := by have := (le_div_iff₀ hη).mp hu.2.le; nlinarith
      simp only [smoothDerivative, cut_of_le hηu, Complex.ofReal_mul, Complex.ofReal_pow]
      ring
    _ = (η : ℂ) ^ n * ((η : ℂ) * (∫ u in (0 : ℝ)..(d / η),
        Complex.exp (-z * (u : ℂ)) * (scaledDerivative n (η * u) : ℂ))) := by
      rw [intervalIntegral.integral_const_mul, pow_succ]
      ring
    _ = _ := by rw [hchange]; rfl

lemma laplace_smoothKernel {η : ℝ} (hη : 0 < η) (z : ℂ) :
    laplace (smoothKernel η) z = W (z / (η : ℂ)) := by
  simpa only [smoothKernel, pow_zero, one_mul, scaledLaplace_zero] using laplace_smoothDerivative 0 hη z

/-- The exact integration-by-parts conversion of Kadiri's raw second-derivative
remainder to W0, with no external analytic input. -/
theorem laplace_second_div_sq {η : ℝ} (hη : 0 < η) {z : ℂ} (hz : z ≠ 0) :
    laplace (deriv (deriv (smoothKernel η))) z / z ^ 2 = W0 (z / (η : ℂ)) := by
  rw [smoothKernel_second, laplace_smoothDerivative 2 hη]
  have hηC : (η : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hη)
  let ξ := z / (η : ℂ)
  have hξ : ξ ≠ 0 := div_ne_zero hz hηC
  have h0 := scaledLaplace_ibp 0 ξ
  have h1 := scaledLaplace_ibp 1 ξ
  have hp0 : scaledDerivative 0 0 = 10 := by rw [scaledDerivative_zero]; exact piece_at_zero
  have hpd : scaledDerivative 0 d = 0 := by rw [scaledDerivative_zero]; exact piece_at_end
  have hp10 := piece_first_zero
  have hp1d := piece_first_end
  rw [iteratedDeriv_piece] at hp10 hp1d
  simp only [scaledLaplace_zero, hp0, hpd, Complex.ofReal_ofNat, Complex.ofReal_zero,
    mul_zero, sub_zero] at h0
  simp only [hp10, hp1d, Complex.ofReal_zero, mul_zero, zero_sub, neg_zero, zero_add] at h1
  have he : scaledLaplace 2 ξ = ξ ^ 2 * W ξ - 10 * ξ := by linear_combination - ξ * h0 - h1
  change (η : ℂ) ^ 2 * scaledLaplace 2 ξ / z ^ 2 = W ξ - 10 / ξ
  rw [he]
  dsimp [ξ]
  field_simp

#print axioms laplace_second_div_sq
end Varlamov.Kernel
