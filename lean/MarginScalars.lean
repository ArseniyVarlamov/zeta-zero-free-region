import PrimeNumberTheoremAnd.IEANTN.Varlamov.MarginExpression
import PrimeNumberTheoremAnd.IEANTN.Varlamov.GammaCertificates
import PrimeNumberTheoremAnd.IEANTN.Varlamov.TailConstants

namespace Varlamov
open Real
open scoped BigOperators

lemma margin_coeffs_length (j : Fin 7) : (MarginExpression.data j).coeffs.length = Multiplier.length j := by
  fin_cases j <;> rfl

lemma margin_coefficients (j : Fin 7) {m : ℕ} (hm : m < Multiplier.length j) :
    (((MarginExpression.data j).coeffs.getD m 0 : ℚ) : ℝ) = Multiplier.coefficient j m := by
  fin_cases j <;> norm_num [Multiplier.length] at hm
  all_goals interval_cases m <;> norm_num [MarginExpression.data, Multiplier.coefficient,
    Multiplier.coefficient1, Multiplier.coefficient2, Multiplier.coefficient3,
    Multiplier.coefficient4, Multiplier.coefficient5, Multiplier.coefficient6, Multiplier.coefficient7]

lemma margin_gamma (j : Fin 7) : ((MarginExpression.data j).gamma : ℝ) = gammaLower j := by
  fin_cases j <;> norm_num [MarginExpression.data, gammaLower]

lemma margin_q (j : Fin 7) : ((MarginExpression.data j).q : ℝ) = gammaQ j := by
  fin_cases j <;> norm_num [MarginExpression.data, gammaQ, aPlus, Multiplier.kappa,
    Multiplier.kappa1, Multiplier.kappa2, Multiplier.kappa3, Multiplier.kappa4,
    Multiplier.kappa5, Multiplier.kappa6, Multiplier.kappa7]

lemma margin_q_lower (j : Fin 7) : (8 : ℝ) ≤ (MarginExpression.data j).q := by
  fin_cases j <;> norm_num [MarginExpression.data]

lemma margin_tail_bound (j : Fin 7) : zeroTailBudget j ≤ (1e-7 : ℝ) := by
  obtain ⟨h0,h1⟩ := tail_constants_small j
  have ha : 0 < aPlus ∧ aPlus < 4 := by norm_num [aPlus]
  have hm := mul_le_mul_of_nonneg_left h1.le ha.1.le
  unfold zeroTailBudget
  nlinarith only [h0, hm, ha.2]

end Varlamov
