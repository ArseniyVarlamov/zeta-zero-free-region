import PrimeNumberTheoremAnd.IEANTN.Varlamov.CheckedDerivatives

/-!
Checked derivative and corner certificates for the rational lower expression
of band 2. The semantic bridge to the actual margin is proved separately.
These checks alone are not the article's C13.
-/

namespace Varlamov.MarginRectangle2
open LeanCert LeanCert.Core

-- The kernel evaluates the complete dyadic interval calculation.
set_option maxRecDepth 32768 in
set_option maxHeartbeats 10000000 in
lemma mu_check : MarginExpression.checkRange 1 (MarginExpression.fullBox 1) 0 (1/10) (1/2) = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 10000000 in
lemma eta_check : MarginExpression.checkRange 1 (MarginExpression.fullBox 1) 1 8 50 = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 10000000 in
lemma corner_check : MarginExpression.checkPositive 1 (MarginExpression.cornerBox 1) (1/1000000) = true := by
  decide +kernel

#print axioms mu_check
#print axioms eta_check
#print axioms corner_check
end Varlamov.MarginRectangle2
