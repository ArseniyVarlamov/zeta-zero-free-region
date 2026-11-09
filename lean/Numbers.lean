import PrimeNumberTheoremAnd.IEANTN.Varlamov.Definitions
import LeanCert.Tactic.IntervalAuto

namespace Varlamov
open Real

/-- Computer check (C1), lower endpoint. -/
lemma Llo_lt_log_H : Llo < log H := by
  unfold Llo H
  interval_decide (trust := kernel)

/-- Computer check (C1), upper endpoint; Yang takes over strictly before Lhi. -/
lemma yang_endpoint : (21.233 : ℝ) * Astar < log Lhi := by
  unfold Astar Lhi
  interval_decide (trust := kernel)

lemma region_boundary_gt_half {t : ℝ} (ht : 2 ≤ t) :
    1 / 2 < 1 - 1 / (R * log t) := by
  have hlog : (0.6931471803 : ℝ) < log t :=
    lt_of_lt_of_le Real.log_two_gt_d9 (Real.log_le_log (by norm_num) ht)
  have hp : 0 < R * log t := mul_pos R_pos (by linarith)
  have hR : 2 < R * log t := by
    dsimp [R]
    nlinarith
  have hdiv : 1 / (R * log t) < (1 / 2 : ℝ) :=
    (div_lt_iff₀ hp).mpr (by nlinarith)
  linarith

end Varlamov
