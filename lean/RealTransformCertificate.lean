import PrimeNumberTheoremAnd.IEANTN.Varlamov.UnitTransform
import PrimeNumberTheoremAnd.IEANTN.Varlamov.SmallArguments

namespace Varlamov
open Real Polynomial
open scoped BigOperators

noncomputable def unitLeft (k : ℕ) : ℝ := ((Polynomial.derivative^[k]) Kernel.unitPoly).eval 0
noncomputable def unitRight (k : ℕ) : ℝ := ((Polynomial.derivative^[k]) Kernel.unitPoly).eval 1

noncomputable def rationalW (z : ℝ) : ℝ :=
  Kernel.d * ∑ k ∈ Finset.range 10, unitLeft k / (Kernel.d * z) ^ (k + 1)
noncomputable def endpointW (z : ℝ) : ℝ :=
  Kernel.d * ∑ k ∈ Finset.range 10, unitRight k / (Kernel.d * z) ^ (k + 1)

lemma realW_exact {z : ℝ} (hz : z ≠ 0) :
    realW z = rationalW z - Real.exp (-Kernel.d * z) * endpointW z := by
  have hzC : (z : ℂ) ≠ 0 := by exact_mod_cast hz
  have hdC : (Kernel.d : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt Kernel.d_pos)
  have he := congrArg (fun v : ℂ => (Kernel.d : ℂ) * v)
    (Kernel.U_exact (mul_ne_zero hdC hzC))
  rw [← Kernel.W_scale] at he
  rw [W_real] at he
  have hreal (k : ℕ) :
      ((Polynomial.derivative^[k]) (Kernel.unitPoly.map Complex.ofRealHom)).eval 0 =
        (unitLeft k : ℂ) := by
    rw [Polynomial.iterate_derivative_map]
    exact Polynomial.eval_map_apply Complex.ofRealHom 0
  have hreal' (k : ℕ) :
      ((Polynomial.derivative^[k]) (Kernel.unitPoly.map Complex.ofRealHom)).eval 1 =
        (unitRight k : ℂ) := by
    rw [Polynomial.iterate_derivative_map]
    exact Polynomial.eval_map_apply Complex.ofRealHom 1
  simp_rw [hreal, hreal'] at he
  have hexp : Complex.exp (-((Kernel.d : ℂ) * (z : ℂ))) =
      (Real.exp (-Kernel.d * z) : ℂ) := by push_cast; congr 1; ring
  rw [hexp] at he
  rw [Finset.mul_sum] at he
  have he' := congrArg Complex.re he
  simp only [← Complex.ofReal_mul, ← Complex.ofReal_sub, ← Complex.ofReal_div,
    ← Complex.ofReal_pow, Complex.re_sum, Complex.ofReal_re] at he'
  dsimp only [rationalW, endpointW]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  convert he' using 1
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma unitRight_abs_bound {k : ℕ} (hk : k < 10) : |unitRight k| ≤ (1e15 : ℝ) := by
  interval_cases k <;> norm_num [unitRight, Kernel.unitPoly, Function.iterate_succ_apply',
    Polynomial.derivative_pow]

lemma endpointW_abs_bound {z : ℝ} (hz : 130 ≤ z) : |endpointW z| ≤ (2e16 : ℝ) := by
  have hd : (1 : ℝ) ≤ Kernel.d ∧ Kernel.d ≤ 2 := by norm_num [Kernel.d]
  have hdz : (1 : ℝ) ≤ Kernel.d * z := by nlinarith
  have hsum : |∑ k ∈ Finset.range 10, unitRight k / (Kernel.d * z) ^ (k + 1)| ≤ (1e16 : ℝ) := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _k ∈ Finset.range 10, (1e15 : ℝ) := by
        apply Finset.sum_le_sum
        intro k hk
        rw [abs_div, abs_of_pos (by positivity : 0 < (Kernel.d * z) ^ (k + 1))]
        apply div_le_of_le_mul₀ (by positivity) (by norm_num)
        exact (unitRight_abs_bound (Finset.mem_range.mp hk)).trans
          (le_mul_of_one_le_right (by norm_num) (one_le_pow₀ hdz))
      _ = _ := by norm_num
  rw [endpointW, abs_mul, abs_of_pos Kernel.d_pos]
  nlinarith only [hsum, hd.2, abs_nonneg
    (∑ k ∈ Finset.range 10, unitRight k / (Kernel.d * z) ^ (k + 1))]

lemma exp_minus_130_small : Real.exp (-130 : ℝ) < (1e-40 : ℝ) := by
  have h : Real.exp (-13 : ℝ) < (1e-4 : ℝ) := by interval_decide (trust := kernel)
  have he : Real.exp (-130 : ℝ) = (Real.exp (-13 : ℝ)) ^ 10 := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [he]
  exact lt_of_lt_of_le (pow_lt_pow_left₀ h (Real.exp_nonneg _) (by norm_num : 10 ≠ 0)) (by norm_num)

/-- A uniform certified comparison with the actual W, for every large real
argument occurring in the seven C13 rectangles. No rounded endpoint data is
assumed. -/
theorem realW_rational_error {z : ℝ} (hz : 130 ≤ z) :
    |realW z - rationalW z| ≤ (1e-20 : ℝ) := by
  have hz0 : z ≠ 0 := by linarith
  have heq : realW z - rationalW z = -Real.exp (-Kernel.d * z) * endpointW z := by
    rw [realW_exact hz0]
    ring
  rw [heq, abs_mul, abs_neg, abs_of_pos (Real.exp_pos _)]
  have hd : (1 : ℝ) ≤ Kernel.d := by norm_num [Kernel.d]
  have he : Real.exp (-Kernel.d * z) ≤ Real.exp (-130 : ℝ) := Real.exp_le_exp.mpr (by nlinarith)
  have hr := endpointW_abs_bound hz
  have he0 := Real.exp_nonneg (-Kernel.d * z)
  have hp := mul_le_mul he hr (abs_nonneg _) (Real.exp_nonneg _)
  have ht := exp_minus_130_small
  nlinarith only [hp, ht]

#print axioms realW_rational_error
end Varlamov
