import PrimeNumberTheoremAnd.IEANTN.Varlamov.MarginCertificates
import PrimeNumberTheoremAnd.IEANTN.Varlamov.ActualMarginLower
import PrimeNumberTheoremAnd.IEANTN.Varlamov.PhaseLowerData
import PrimeNumberTheoremAnd.IEANTN.Varlamov.RemainderNumerical

namespace Varlamov
open Real

/-- C13 for the actual Theta on all seven closed rectangles. The only input
here is the explicitly named published real digamma remainder (Nemes 2017).
Every numerical phase-budget, gamma, remainder, endpoint, moment, derivative,
corner, and coverage inequality used in this proof is checked in Lean. -/
@[blueprint "varlamov-actual-margin-certificate"
  (title := "Varlamov, Proposition 8.3: actual margin on all seven rectangles")
  (statement := /-- With the published real digamma remainder as an explicit
  input, the actual margin for the concrete rational prime-phase lower bounds
  exceeds $10^{-6}$ on every closed band rectangle. All scalar enclosures,
  moment and exact-transform comparisons, derivative checks, corner bounds,
  and coverage arguments are proved in Lean. -/)
  (uses := ["varlamov-exact-transform", "varlamov-moment-enclosures",
    "varlamov-large-arguments", "varlamov-tail-constants"])]
theorem actual_margin_certificate (hS : RealDigammaStirlingInput) : MarginCertificate phaseLower := by
  intro j L A hb
  have hG : ((MarginExpression.data j).gamma : ℝ) ≤ gammaG j := by
    rw [margin_gamma]
    exact gammaLower_le hS j
  have hl := MarginExpression.value_le_margin j (phaseLower j) hG (primeLower_numeric j)
    (remainderE_upper j) (margin_tail_bound j) hb
  exact (MarginExpression.rational_margin_positive j hb).trans_le hl

#print axioms actual_margin_certificate
end Varlamov
