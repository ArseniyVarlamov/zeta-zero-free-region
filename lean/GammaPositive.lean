import PrimeNumberTheoremAnd.IEANTN.Varlamov.GammaLedger

namespace Varlamov
open Real
open scoped BigOperators

lemma euler_constant_lt_three_fifths : Real.eulerMascheroniConstant < (3 / 5 : ℝ) := by
  apply (Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' 30).trans
  norm_num [Real.eulerMascheroniSeq', harmonic, Finset.sum_range_succ]
  interval_decide (trust := kernel)

lemma sigmaMax_range (j : Fin 7) : 0.99 < sigmaMax j ∧ sigmaMax j < 1 := by
  have hL : (28 : ℝ) < bandHi j := by
    have h := bandLo_ge j
    have he := band_endpoints j
    norm_num [Llo] at h
    linarith
  have hl : 28 < logCutoff (bandHi j) := hL.trans logCutoff_gt
  have hp : 0 < logCutoff (bandHi j) := by linarith
  have hd : 0 < (1 / 6 : ℝ) / logCutoff (bandHi j) := div_pos (by norm_num) hp
  have hu : (1 / 6 : ℝ) / logCutoff (bandHi j) < 0.01 := (div_lt_iff₀ hp).mpr (by linarith)
  unfold sigmaMax
  constructor <;> linarith

noncomputable def integerGammaUpper (j : Fin 7) (m : ℕ) : ℝ := Multiplier.coefficient j m *
  (if 0 < Multiplier.coefficient j m then ((harmonic ((m + 4) / 2 - 1) : ℚ) : ℝ) - 1 / 2
    else ((harmonic (m / 2) : ℚ) : ℝ) - 3 / 5)

lemma realDigamma_integer (n : ℕ) : realDigamma ((n : ℝ) + 1) =
    ((harmonic n : ℚ) : ℝ) - Real.eulerMascheroniConstant := by
  unfold realDigamma
  have he := Complex.digamma_nat_add_one n
  have he' := congrArg Complex.re he
  simpa using he'

lemma integerGammaUpper_bound (j : Fin 7) {m : ℕ} (hm : m ≤ 14) :
    Multiplier.coefficient j m * realDigamma (gammaX j m) ≤ integerGammaUpper j m := by
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hg : 0 < gammaX j m := by
    have hσ := (sigmaMin_range j).1
    have hu := (sigmaMax_range j).1
    have hh := hMin_pos j
    unfold gammaX
    split_ifs <;> nlinarith
  have hσu := (sigmaMax_range j).2
  have hσl := (sigmaMin_range j).1
  have hhl : (0.98 : ℝ) < hMin j := by unfold hMin; linarith
  unfold integerGammaUpper
  by_cases hc : 0 < Multiplier.coefficient j m
  · rw [ite_eq_left hc]
    have harg : gammaX j m ≤ (((m + 4) / 2 - 1 : ℕ) : ℝ) + 1 := by
      simp only [gammaX, ite_eq_left hc]
      interval_cases m <;> norm_num <;> nlinarith
    have hn : (0 : ℝ) < (((m + 4) / 2 - 1 : ℕ) : ℝ) + 1 := by positivity
    have hp := realDigamma_monotoneOn hg hn harg
    rw [realDigamma_integer] at hp
    exact mul_le_mul_of_nonneg_left (by linarith [Real.one_half_lt_eulerMascheroniConstant]) hc.le
  · rw [ite_eq_right hc]
    have harg : ((m / 2 : ℕ) : ℝ) + 1 ≤ gammaX j m := by
      simp only [gammaX, ite_eq_right hc]
      interval_cases m <;> norm_num <;> nlinarith
    have hn : (0 : ℝ) < ((m / 2 : ℕ) : ℝ) + 1 := by positivity
    have hp := realDigamma_monotoneOn hn hg harg
    rw [realDigamma_integer] at hp
    exact mul_le_mul_of_nonpos_left (by linarith [euler_constant_lt_three_fifths]) (le_of_not_gt hc)

lemma gammaLogMoment_upper : gammaLogMoment < (1.53 : ℝ) := by
  norm_num [gammaLogMoment, Trigonometric.a, Finset.sum_range_succ]
  interval_decide (trust := kernel)
lemma log_pi_lower : (1.14 : ℝ) < Real.log Real.pi := by interval_decide (trust := kernel)
lemma log_two_pi_lower : (1.83 : ℝ) < Real.log (2 * Real.pi) := by
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt Real.pi_pos)]
  have h2 : (0.69 : ℝ) < Real.log 2 := by interval_decide (trust := kernel)
  linarith [log_pi_lower]

noncomputable def gammaCoarseLower (j : Fin 7) : ℝ :=
  - (1 / 2) * (∑ m ∈ Finset.range (Multiplier.length j), integerGammaUpper j m) +
    (Multiplier.kappa j 1 / 2) * 1.14 - (Multiplier.kappa j 1 / 2) * 1.53 +
    (aPlus * Multiplier.kappa j 1 / 2) * 1.83 - (aPlus * Multiplier.coeffNorm j / 2) * 1e-10

lemma gammaCoarseLower_pos (j : Fin 7) : 0 < gammaCoarseLower j := by
  fin_cases j <;> norm_num [gammaCoarseLower, integerGammaUpper, harmonic,
    Multiplier.length, Multiplier.coefficient, Multiplier.coeffNorm, Multiplier.kappa,
    Multiplier.kappa1, Multiplier.kappa2, Multiplier.kappa3, Multiplier.kappa4,
    Multiplier.kappa5, Multiplier.kappa6, Multiplier.kappa7,
    Multiplier.coefficient1, Multiplier.coefficient2, Multiplier.coefficient3,
    Multiplier.coefficient4, Multiplier.coefficient5, Multiplier.coefficient6,
    Multiplier.coefficient7, aPlus, Finset.sum_range_succ]

/-- Check C8: positivity of the article's actual G in every band. The proof
uses coarse integer digamma bounds; it does not assume numerical digamma data. -/
theorem gammaG_pos (j : Fin 7) : 0 < gammaG j := by
  have hκ : 0 < Multiplier.kappa j 1 := Multiplier.kappa_pos j ⟨by norm_num, le_rfl⟩
  have ha : 0 < aPlus := by norm_num [aPlus]
  have hsum : (∑ m ∈ Finset.range (Multiplier.length j), Multiplier.coefficient j m * realDigamma (gammaX j m)) ≤
      ∑ m ∈ Finset.range (Multiplier.length j), integerGammaUpper j m := by
    apply Finset.sum_le_sum
    intro m hm
    have := Finset.mem_range.mp hm
    have := degree_upper j
    apply integerGammaUpper_bound j
    omega
  apply (gammaCoarseLower_pos j).trans_le
  unfold gammaG gammaCoarseLower
  have h1 := mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have h2 := mul_le_mul_of_nonneg_left log_pi_lower.le (by positivity : (0 : ℝ) ≤ Multiplier.kappa j 1 / 2)
  have h3 := mul_le_mul_of_nonneg_left gammaLogMoment_upper.le (by positivity : (0 : ℝ) ≤ Multiplier.kappa j 1 / 2)
  have h4 := mul_le_mul_of_nonneg_left log_two_pi_lower.le (by positivity : (0 : ℝ) ≤ aPlus * Multiplier.kappa j 1 / 2)
  linarith

#print axioms gammaG_pos
end Varlamov
