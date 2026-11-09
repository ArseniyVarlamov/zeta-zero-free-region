import PrimeNumberTheoremAnd.IEANTN.Varlamov.MarginDomain

namespace Varlamov.MarginExpression
open LeanCert LeanCert.Core

set_option maxHeartbeats 3000000 in
-- Several closed interval certificates and their exact rational transports
-- are checked together in this finite seven-band declaration.
lemma cornerBox_mem (j : Fin 7) :
    BoxEnvMem (environment (mu (bandHi j)) (eta (bandHi j) Astar) Astar) (cornerBox j) := by
  intro i
  rcases i with _ | i
  · fin_cases j <;> norm_num [environment, cornerBox, IntervalRat.mem_def, mu, logCutoff, bandHi] <;>
      constructor <;> interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring
  rcases i with _ | i
  · fin_cases j <;> norm_num [environment, cornerBox, IntervalRat.mem_def, eta, Astar, bandHi]
  rcases i with _ | i
  · fin_cases j <;> norm_num [environment, cornerBox, IntervalRat.mem_def, Astar]
  · fin_cases j <;> simp [environment, cornerBox, IntervalRat.mem_def, IntervalRat.singleton]

end Varlamov.MarginExpression
