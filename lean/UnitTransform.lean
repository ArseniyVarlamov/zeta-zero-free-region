import PrimeNumberTheoremAnd.IEANTN.Varlamov.ExactTransform
import PrimeNumberTheoremAnd.IEANTN.Varlamov.KernelSupport
import Mathlib.Analysis.Complex.Trigonometric

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace Varlamov.Kernel
open Real Polynomial MeasureTheory
open scoped Polynomial BigOperators

noncomputable def U (z : ℂ) : ℂ :=
  ∫ u in (0 : ℝ)..1, Complex.exp (-z * (u : ℂ)) * (unit u : ℂ)

lemma unitPoly_natDegree : unitPoly.natDegree = 9 := by
  unfold unitPoly
  compute_degree <;> norm_num

lemma unitPoly_degree : unitPoly.natDegree < 10 := by
  unfold unitPoly
  compute_degree ; norm_num

lemma unitMap_eval (u : ℝ) : (unitPoly.map Complex.ofRealHom).eval (u : ℂ) = (unit u : ℂ) := by
  exact Polynomial.eval_map_apply Complex.ofRealHom u

lemma U_exact {z : ℂ} (hz : z ≠ 0) :
    U z = ∑ k ∈ Finset.range 10,
      (((Polynomial.derivative^[k]) (unitPoly.map Complex.ofRealHom)).eval 0 -
        Complex.exp (-z) * ((Polynomial.derivative^[k]) (unitPoly.map Complex.ofRealHom)).eval 1) /
          z ^ (k + 1) := by
  have hp : (unitPoly.map Complex.ofRealHom).natDegree < 10 :=
    natDegree_map_le.trans_lt unitPoly_degree
  have h := polynomial_laplace_exact (unitPoly.map Complex.ofRealHom) hp hz 1
  simpa only [U, unitMap_eval, Complex.ofReal_one, mul_one] using h

lemma W_scale (z : ℂ) : W z = (d : ℂ) * U ((d : ℂ) * z) := by
  have h := intervalIntegral.smul_integral_comp_mul_left
    (fun u : ℝ => Complex.exp (-z * (u : ℂ)) * (piece u : ℂ)) (a := 0) (b := 1) d
  have hd : d ≠ 0 := ne_of_gt d_pos
  have hf (u : ℝ) : Complex.exp (-z * ((d * u : ℝ) : ℂ)) * (piece (d * u) : ℂ) =
      Complex.exp (-((d : ℂ) * z) * (u : ℂ)) * (unit u : ℂ) := by
    have hpiece : piece (d * u) = unit u := by simp [piece, hd]
    rw [hpiece]
    push_cast
    congr 2
    ring
  simp_rw [hf] at h
  simpa only [U, W, mul_zero, mul_one, Complex.real_smul] using h.symm

lemma U_zero_nonneg : 0 ≤ (U 0).re := by
  have h : U 0 = (((∫ u in (0 : ℝ)..1, unit u) : ℝ) : ℂ) := by
    simp [U, intervalIntegral.integral_ofReal]
  rw [h, Complex.ofReal_re]
  exact intervalIntegral.integral_nonneg (by norm_num) unit_nonneg

/-- Exact cosine-square factor of the autocorrelation transform, expressed
using the quartic q. This is a direct finite algebraic check of the Fourier sign. -/
noncomputable def cosineFactor (x : ℝ) : ℝ :=
  ((-2 * (b + 1) * x ^ 3 + 24 * b * x) * Real.cos x + ((10 * b + 2) * x ^ 2 - 24 * b) * Real.sin x) / x ^ 5

lemma U_imaginary_square {y : ℝ} (hy : y ≠ 0) :
    (U ((y : ℂ) * Complex.I)).re = (10 / qnorm) * (cosineFactor (y / 2)) ^ 2 := by
  have hz : (y : ℂ) * Complex.I ≠ 0 := mul_ne_zero (by exact_mod_cast hy) Complex.I_ne_zero
  have hexp : Complex.exp (-((y : ℂ) * Complex.I)) =
      (Real.cos y : ℂ) - (Real.sin y : ℂ) * Complex.I := by
    rw [show - ((y : ℂ) * Complex.I) = (((-y : ℝ) : ℂ) * Complex.I) from by push_cast; ring,
      Complex.exp_ofReal_mul_I]
    simp [sub_eq_add_neg]
  rw [U_exact hz]
  norm_num [Finset.sum_range_succ, unitPoly, Function.iterate_succ_apply',
    Polynomial.derivative_pow, mul_pow, ← Complex.ofReal_pow, Complex.I_sq, hexp,
    Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.mul_im, Complex.div_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.normSq_apply,
    Complex.cos_ofReal_re, Complex.sin_ofReal_re]
  have hc : Real.cos y = 2 * (Real.cos (y / 2)) ^ 2 - 1 := by
    convert Real.cos_two_mul (y / 2) using 1 <;> congr 1 <;> ring
  have hs : Real.sin y = 2 * Real.sin (y / 2) * Real.cos (y / 2) := by
    convert Real.sin_two_mul (y / 2) using 1 <;> congr 1 <;> ring
  have hsc : (Real.sin (y * (1 / 2))) ^ 2 = 1 - (Real.cos (y * (1 / 2))) ^ 2 := by
    nlinarith [sin_sq_add_cos_sq (y * (1 / 2))]
  rw [hc, hs]
  unfold cosineFactor b qnorm
  field_simp
  ring_nf
  simp_rw [hsc]
  ring

lemma U_imaginary_nonneg (y : ℝ) : 0 ≤ (U ((y : ℂ) * Complex.I)).re := by
  by_cases hy : y = 0
  · simpa [hy] using U_zero_nonneg
  · rw [U_imaginary_square hy]
    exact mul_nonneg (div_nonneg (by norm_num) qnorm_pos.le) (sq_nonneg _)

@[blueprint "varlamov-transform-fourier-positive"
  (title := "Varlamov, Lemma 4.1(4): nonnegative real part on the imaginary axis")
  (statement := /-- The real part of $W(iy)$ is nonnegative for every real y.
  Here this is proved from the finite exact transform and a cosine-square identity,
  rather than by invoking a general convolution theorem. -/)
  (uses := ["varlamov-exact-transform", "varlamov-kernel-autocorrelation"])]
theorem W_imaginary_nonneg (y : ℝ) : 0 ≤ (W ((y : ℂ) * Complex.I)).re := by
  rw [W_scale]
  rw [show (d : ℂ) * ((y : ℂ) * Complex.I) = ((d * y : ℝ) : ℂ) * Complex.I from by push_cast; ring]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_nonneg d_pos.le (U_imaginary_nonneg (d * y))

#print axioms W_imaginary_nonneg

end Varlamov.Kernel
