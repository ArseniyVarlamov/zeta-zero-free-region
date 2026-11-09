import PrimeNumberTheoremAnd.IEANTN.Varlamov.RemainderLedger

namespace Varlamov
open Real
open scoped BigOperators

lemma C_uniform_upper {ν : ℝ} (hν : 400 ≤ ν) : Kernel.C ν ≤ (91 : ℝ) := by
  have hν0 : 0 < ν := by linarith
  have he : Real.exp (-ν * Kernel.d) ≤ 1 := Real.exp_le_one_iff.mpr
    (by have hd := Kernel.d_pos; nlinarith)
  have hp := Kernel.scaled_third_pos
  have hM := Kernel.M4star_pos
  unfold Kernel.C
  calc
    _ ≤ |Kernel.scaledDerivative 2 0| + Kernel.scaledDerivative 3 0 * 2 / 400 + Kernel.M4star / 400 ^ 2 := by
      gcongr <;> nlinarith
    _ ≤ _ := by
      norm_num [Kernel.scaledDerivative, Kernel.unitPoly, Kernel.d, Kernel.M4star,
        Kernel.unitM4, Function.iterate_succ_apply', Polynomial.derivative_pow]

lemma remainderC_upper (j : Fin 7) (m : ℕ) : remainderC j m ≤ (91 : ℝ) := by
  have hη : etaMax j ≤ (37 / 5000 : ℝ) := by fin_cases j <;> norm_num [etaMax]
  have hu : (299 / 100 : ℝ) < remainderU j m := by
    unfold remainderU
    have hσ := (sigmaMin_range j).1
    have hh := hMin_pos j
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    nlinarith
  unfold remainderC
  apply C_uniform_upper
  apply (le_div_iff₀ (etaMax_range j).1).mpr
  nlinarith

noncomputable def remainderBase (j : Fin 7) : ℝ :=
  ∑ m ∈ Finset.range (Multiplier.length j), |Multiplier.coefficient j m| *
    (1 / (remainderU j m) ^ 3 + 1 / (4 * (remainderU j m) ^ 2) +
      aPlus * (1 / H ^ 3 + 1 / (2 * H ^ 2)))

lemma remainderE_le_base (j : Fin 7) : remainderE j ≤ 91 * remainderBase j := by
  unfold remainderE remainderBase
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro m _
  have hU := remainderU_pos j m
  have hH : (0 : ℝ) < H := by norm_num [H]
  have ha : (0 : ℝ) < aPlus := by norm_num [aPlus]
  have hb : 0 ≤ |Multiplier.coefficient j m| *
      (1 / (remainderU j m) ^ 3 + 1 / (4 * (remainderU j m) ^ 2) +
        aPlus * (1 / H ^ 3 + 1 / (2 * H ^ 2))) := by positivity
  have h := mul_le_mul_of_nonneg_right (remainderC_upper j m) hb
  convert h using 1 <;> ring

-- The remaining enclosure is purely rational; no exponential interval
-- evaluation is needed for any of the seven bands.
set_option maxHeartbeats 3000000 in
lemma remainderBase_upper (j : Fin 7) : 91 * remainderBase j ≤ (13 : ℝ) := by
  fin_cases j <;> norm_num [remainderBase, remainderU, sigmaMin, hMin, H, aPlus,
    Multiplier.length, Multiplier.coefficient, Multiplier.coefficient1,
    Multiplier.coefficient2, Multiplier.coefficient3, Multiplier.coefficient4,
    Multiplier.coefficient5, Multiplier.coefficient6, Multiplier.coefficient7,
    Finset.sum_range_succ]

theorem remainderE_upper (j : Fin 7) : remainderE j ≤ (13 : ℝ) :=
  (remainderE_le_base j).trans (remainderBase_upper j)

#print axioms remainderE_upper
end Varlamov
