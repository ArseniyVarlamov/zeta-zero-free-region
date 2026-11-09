import PrimeNumberTheoremAnd.IEANTN.Varlamov.MarginMonotone
import PrimeNumberTheoremAnd.IEANTN.Varlamov.MarginCornerDomain
import PrimeNumberTheoremAnd.IEANTN.Varlamov.MarginRectangle1
import PrimeNumberTheoremAnd.IEANTN.Varlamov.MarginRectangle2
import PrimeNumberTheoremAnd.IEANTN.Varlamov.MarginRectangle3
import PrimeNumberTheoremAnd.IEANTN.Varlamov.MarginRectangle4
import PrimeNumberTheoremAnd.IEANTN.Varlamov.MarginRectangle5
import PrimeNumberTheoremAnd.IEANTN.Varlamov.MarginRectangle6
import PrimeNumberTheoremAnd.IEANTN.Varlamov.MarginRectangle7

namespace Varlamov.MarginExpression
open LeanCert LeanCert.Core

lemma all_mu_checks (j : Fin 7) : checkRange j (fullBox j) 0 (1/10) (1/2) = true := by
  fin_cases j
  · exact MarginRectangle1.mu_check
  · exact MarginRectangle2.mu_check
  · exact MarginRectangle3.mu_check
  · exact MarginRectangle4.mu_check
  · exact MarginRectangle5.mu_check
  · exact MarginRectangle6.mu_check
  · exact MarginRectangle7.mu_check

lemma all_eta_checks (j : Fin 7) : checkRange j (fullBox j) 1 8 50 = true := by
  fin_cases j
  · exact MarginRectangle1.eta_check
  · exact MarginRectangle2.eta_check
  · exact MarginRectangle3.eta_check
  · exact MarginRectangle4.eta_check
  · exact MarginRectangle5.eta_check
  · exact MarginRectangle6.eta_check
  · exact MarginRectangle7.eta_check

lemma all_corner_checks (j : Fin 7) : checkPositive j (cornerBox j) (1/1000000) = true := by
  fin_cases j
  · exact MarginRectangle1.corner_check
  · exact MarginRectangle2.corner_check
  · exact MarginRectangle3.corner_check
  · exact MarginRectangle4.corner_check
  · exact MarginRectangle5.corner_check
  · exact MarginRectangle6.corner_check
  · exact MarginRectangle7.corner_check

/-- All seven full closed rectangles for the lower expression. Its exact
comparison with the actual Theta is proved in ActualMarginLower. -/
theorem rational_margin_positive (j : Fin 7) {L A : ℝ} (hb : InBand j L A) :
    (1e-6 : ℝ) < value j (mu L) (eta L A) A := by
  have hc := positive_correct j (cornerBox j) (1/1000000) (all_corner_checks j) (cornerBox_mem j)
  have hc' : (1e-6 : ℝ) < value j (mu (bandHi j)) (eta (bandHi j) Astar) Astar := by
    convert hc using 1 <;> norm_num [value]
  exact hc'.trans_le (value_corner_le j (all_mu_checks j) (all_eta_checks j) hb)

#print axioms rational_margin_positive
end Varlamov.MarginExpression
