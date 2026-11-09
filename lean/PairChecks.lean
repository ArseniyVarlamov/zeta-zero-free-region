import PrimeNumberTheoremAnd.IEANTN.Varlamov.TransformDecay
import PrimeNumberTheoremAnd.IEANTN.Varlamov.MultiplierData

set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

namespace Varlamov
open Real

noncomputable def hMin (j : Fin 7) : ℝ := 2 * sigmaMin j - 1
noncomputable def nuMin (j : Fin 7) : ℝ := hMin j / etaMax j

lemma hMin_pos (j : Fin 7) : 0 < hMin j := by
  unfold hMin
  linarith [(sigmaMin_range j).1]
lemma nuMin_pos (j : Fin 7) : 0 < nuMin j := div_pos (hMin_pos j) (etaMax_range j).1

/-- Uniformly discard the tiny exponential part with a single certified bound. -/
lemma pair_exp_small : exp (-140 : ℝ) < (1e-50 : ℝ) := by
  interval_decide (trust := kernel)

noncomputable def pairCUpper (ν : ℝ) : ℝ := |Kernel.scaledDerivative 2 0| +
  Kernel.scaledDerivative 3 0 * (1 + 1e-50) / ν + Kernel.M4star / ν ^ 2

lemma pairC_le_upper (j : Fin 7) : Kernel.C (nuMin j) ≤ pairCUpper (nuMin j) := by
  have h140 : (140 : ℝ) ≤ nuMin j * Kernel.d := by
    fin_cases j <;> norm_num [nuMin, hMin, sigmaMin, etaMax, Kernel.d]
  have he : exp (-nuMin j * Kernel.d) ≤ (1e-50 : ℝ) :=
    (exp_le_exp.mpr (by linarith)).trans pair_exp_small.le
  unfold Kernel.C pairCUpper
  apply add_le_add _ le_rfl
  apply add_le_add le_rfl
  apply div_le_div_of_nonneg_right _ (nuMin_pos j).le
  exact mul_le_mul_of_nonneg_left (by linarith) Kernel.scaled_third_pos.le

lemma pair_second_value : Kernel.scaledDerivative 2 0 =
    (-803357971194757140 / 8116714872719329 : ℝ) / Kernel.d ^ 2 := by
  norm_num [Kernel.scaledDerivative, Kernel.unitPoly,
    Function.iterate_succ_apply', Polynomial.derivative_pow]

lemma pair_third_value : Kernel.scaledDerivative 3 0 =
    (1949476490131772700 / 8116714872719329 : ℝ) / Kernel.d ^ 3 := by
  norm_num [Kernel.scaledDerivative, Kernel.unitPoly,
    Function.iterate_succ_apply', Polynomial.derivative_pow]

/-- Check C6. After the common exponential bound, all seven checks are rational. -/
lemma pair_error_numeric (j : Fin 7) :
    Kernel.C (nuMin j) * (etaMax j) ^ 2 < pairedEps j * (hMin j) ^ 2 * 10 := by
  apply lt_of_le_of_lt (mul_le_mul_of_nonneg_right (pairC_le_upper j) (sq_nonneg _))
  unfold pairCUpper
  rw [pair_second_value, pair_third_value]
  fin_cases j <;> norm_num [nuMin, hMin, sigmaMin, etaMax, pairedEps,
    Kernel.M4star, Kernel.unitM4, Kernel.d]

lemma pair_error_bound (j : Fin 7) {h η : ℝ}
    (hh : hMin j ≤ h) (hη : 0 < η) (hηmax : η ≤ etaMax j) :
    Kernel.C (nuMin j) * η ^ 2 < pairedEps j * h ^ 2 * 10 := by
  have hη2 : η ^ 2 ≤ (etaMax j) ^ 2 := by nlinarith [(etaMax_range j).1]
  have hh2 : (hMin j) ^ 2 ≤ h ^ 2 := by nlinarith [hMin_pos j]
  calc
    _ ≤ Kernel.C (nuMin j) * (etaMax j) ^ 2 :=
      mul_le_mul_of_nonneg_left hη2 (Kernel.C_pos (nuMin_pos j)).le
    _ < pairedEps j * (hMin j) ^ 2 * 10 := pair_error_numeric j
    _ ≤ pairedEps j * h ^ 2 * 10 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hh2 (pairedEps_range j).1.le) (by norm_num)

#print axioms pair_error_numeric

end Varlamov
