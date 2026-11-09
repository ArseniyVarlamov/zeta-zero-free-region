import PrimeNumberTheoremAnd.IEANTN.Varlamov.DigammaNumerical

namespace Varlamov
open Real
open scoped BigOperators
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000

noncomputable def gammaLower (j : Fin 7) : ℝ :=
  match j.val with
  | 0 => (1551288 / 1000000 : ℝ)
  | 1 => (1553453 / 1000000 : ℝ)
  | 2 => (1554366 / 1000000 : ℝ)
  | 3 => (1554745 / 1000000 : ℝ)
  | 4 => (1555078 / 1000000 : ℝ)
  | 5 => (1555168 / 1000000 : ℝ)
  | _ => (1555337 / 1000000 : ℝ)

noncomputable def sigmaUpper (j : Fin 7) : ℝ :=
  match j.val with
  | 0 => (1245612641 / 1250000000 : ℝ)
  | 1 => (2493331723 / 2500000000 : ℝ)
  | 2 => (2494251677 / 2500000000 : ℝ)
  | 3 => (9979031659 / 10000000000 : ℝ)
  | 4 => (2494948571 / 2500000000 : ℝ)
  | 5 => (9980272611 / 10000000000 : ℝ)
  | _ => (1996069441 / 2000000000 : ℝ)

lemma sigmaMax_le_upper (j : Fin 7) : sigmaMax j ≤ sigmaUpper j := by
  fin_cases j <;> norm_num [sigmaUpper, sigmaMax, logCutoff, bandHi] <;>
    interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;>
      simp only [mul_comm, LeanCert.Core.MathConst.toReal] <;> ring

noncomputable def gammaNumericX (j : Fin 7) (m : ℕ) : ℝ :=
  if 0 < Multiplier.coefficient j m then
    (sigmaUpper j + (2 * sigmaUpper j - 1) * (m : ℝ)) / 2 + 1
  else gammaX j m

lemma gammaX_le_numeric (j : Fin 7) (m : ℕ) : gammaX j m ≤ gammaNumericX j m := by
  have hu := sigmaMax_le_upper j
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  unfold gammaNumericX
  split_ifs with hc
  · simp only [gammaX, ite_eq_left hc]
    nlinarith
  · exact le_rfl

lemma gamma_numeric_coefficient (hS : RealDigammaStirlingInput) (j : Fin 7) (m : ℕ) :
    Multiplier.coefficient j m * realDigamma (gammaX j m) ≤
      Multiplier.coefficient j m * digammaApprox (gammaNumericX j m) +
        |Multiplier.coefficient j m| * 1e-9 := by
  have hx : 1 ≤ gammaNumericX j m := (gammaX_ge_one j m).trans (gammaX_le_numeric j m)
  have he := digammaApprox_error hS hx
  have h := mul_le_mul_of_nonneg_left he (abs_nonneg (Multiplier.coefficient j m))
  rw [← abs_mul] at h
  have hl := (le_abs_self (Multiplier.coefficient j m *
    (realDigamma (gammaNumericX j m) - digammaApprox (gammaNumericX j m)))).trans h
  have hm : Multiplier.coefficient j m * realDigamma (gammaX j m) ≤
      Multiplier.coefficient j m * realDigamma (gammaNumericX j m) := by
    by_cases hc : 0 < Multiplier.coefficient j m
    · apply mul_le_mul_of_nonneg_left _ hc.le
      have hg0 : 0 < gammaX j m := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (gammaX_ge_one j m)
      have hn0 : 0 < gammaNumericX j m := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hx
      have hψ : realDigamma (gammaX j m) ≤ realDigamma (gammaNumericX j m) :=
        realDigamma_monotoneOn hg0 hn0 (gammaX_le_numeric j m)
      exact hψ
    · simpa only [gammaNumericX, ite_eq_right hc] using
        (le_rfl : Multiplier.coefficient j m * realDigamma (gammaX j m) ≤
          Multiplier.coefficient j m * realDigamma (gammaX j m))
  nlinarith only [hm,hl]

noncomputable def gammaNumericLower (j : Fin 7) : ℝ := -(
  (1 / 2) * (∑ m ∈ Finset.range (Multiplier.length j),
    Multiplier.coefficient j m * digammaApprox (gammaNumericX j m)) -
  (Multiplier.kappa j 1 / 2) * Real.log Real.pi + (Multiplier.kappa j 1 / 2) * gammaLogMoment -
  (aPlus * Multiplier.kappa j 1 / 2) * Real.log (2 * Real.pi) +
  (aPlus * Multiplier.coeffNorm j / 2) * 1e-10 + (Multiplier.coeffNorm j / 2) * 1e-9)

lemma gammaNumericLower_le (hS : RealDigammaStirlingInput) (j : Fin 7) :
    gammaNumericLower j ≤ gammaG j := by
  have hs := Finset.sum_le_sum (fun m (_ : m ∈ Finset.range (Multiplier.length j)) =>
    gamma_numeric_coefficient hS j m)
  rw [Finset.sum_add_distrib, ← Finset.sum_mul] at hs
  change (∑ m ∈ Finset.range (Multiplier.length j),
      Multiplier.coefficient j m * realDigamma (gammaX j m)) ≤
    (∑ m ∈ Finset.range (Multiplier.length j),
      Multiplier.coefficient j m * digammaApprox (gammaNumericX j m)) + Multiplier.coeffNorm j * 1e-9 at hs
  unfold gammaNumericLower gammaG
  linarith only [hs]

lemma gammaLower_le_numeric (j : Fin 7) : gammaLower j ≤ gammaNumericLower j := by
  fin_cases j
  · norm_num [gammaLower, gammaNumericLower, digammaApprox, gammaNumericX, gammaX,
      sigmaUpper, sigmaMin, hMin, Multiplier.length, Multiplier.coefficient,
      Multiplier.coefficient1, Multiplier.kappa, Multiplier.kappa1, Multiplier.coeffNorm,
      gammaLogMoment, Trigonometric.a, aPlus, Finset.sum_range_succ]
    interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;>
      simp only [mul_comm, LeanCert.Core.MathConst.toReal] <;> ring
  · norm_num [gammaLower, gammaNumericLower, digammaApprox, gammaNumericX, gammaX,
      sigmaUpper, sigmaMin, hMin, Multiplier.length, Multiplier.coefficient,
      Multiplier.coefficient2, Multiplier.kappa, Multiplier.kappa2, Multiplier.coeffNorm,
      gammaLogMoment, Trigonometric.a, aPlus, Finset.sum_range_succ]
    interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;>
      simp only [mul_comm, LeanCert.Core.MathConst.toReal] <;> ring
  · norm_num [gammaLower, gammaNumericLower, digammaApprox, gammaNumericX, gammaX,
      sigmaUpper, sigmaMin, hMin, Multiplier.length, Multiplier.coefficient,
      Multiplier.coefficient3, Multiplier.kappa, Multiplier.kappa3, Multiplier.coeffNorm,
      gammaLogMoment, Trigonometric.a, aPlus, Finset.sum_range_succ]
    interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;>
      simp only [mul_comm, LeanCert.Core.MathConst.toReal] <;> ring
  · norm_num [gammaLower, gammaNumericLower, digammaApprox, gammaNumericX, gammaX,
      sigmaUpper, sigmaMin, hMin, Multiplier.length, Multiplier.coefficient,
      Multiplier.coefficient4, Multiplier.kappa, Multiplier.kappa4, Multiplier.coeffNorm,
      gammaLogMoment, Trigonometric.a, aPlus, Finset.sum_range_succ]
    interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;>
      simp only [mul_comm, LeanCert.Core.MathConst.toReal] <;> ring
  · norm_num [gammaLower, gammaNumericLower, digammaApprox, gammaNumericX, gammaX,
      sigmaUpper, sigmaMin, hMin, Multiplier.length, Multiplier.coefficient,
      Multiplier.coefficient5, Multiplier.kappa, Multiplier.kappa5, Multiplier.coeffNorm,
      gammaLogMoment, Trigonometric.a, aPlus, Finset.sum_range_succ]
    interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;>
      simp only [mul_comm, LeanCert.Core.MathConst.toReal] <;> ring
  · norm_num [gammaLower, gammaNumericLower, digammaApprox, gammaNumericX, gammaX,
      sigmaUpper, sigmaMin, hMin, Multiplier.length, Multiplier.coefficient,
      Multiplier.coefficient6, Multiplier.kappa, Multiplier.kappa6, Multiplier.coeffNorm,
      gammaLogMoment, Trigonometric.a, aPlus, Finset.sum_range_succ]
    interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;>
      simp only [mul_comm, LeanCert.Core.MathConst.toReal] <;> ring
  · norm_num [gammaLower, gammaNumericLower, digammaApprox, gammaNumericX, gammaX,
      sigmaUpper, sigmaMin, hMin, Multiplier.length, Multiplier.coefficient,
      Multiplier.coefficient7, Multiplier.kappa, Multiplier.kappa7, Multiplier.coeffNorm,
      gammaLogMoment, Trigonometric.a, aPlus, Finset.sum_range_succ]
    interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;>
      simp only [mul_comm, LeanCert.Core.MathConst.toReal] <;> ring

theorem gammaLower_le (hS : RealDigammaStirlingInput) (j : Fin 7) : gammaLower j ≤ gammaG j :=
  (gammaLower_le_numeric j).trans (gammaNumericLower_le hS j)

#print axioms gammaLower_le
end Varlamov
