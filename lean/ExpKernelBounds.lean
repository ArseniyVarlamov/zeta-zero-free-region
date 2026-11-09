import PrimeNumberTheoremAnd.IEANTN.Varlamov.SmallArguments

namespace Varlamov
open Real
open scoped BigOperators
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

noncomputable def expDLow : ℝ := (1434501897845863237124803522416729232140948046560179734272304752873709 / 500000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def expDHigh : ℝ := (28690037956917264742496070448334584642818960931203594685446095057474181 / 10000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)

/-- A single common 70-decimal enclosure of exp(d), proved by the real
Taylor estimate and rational arithmetic. No external numerical oracle. -/
theorem exp_d_bounds : expDLow ≤ Real.exp Kernel.d ∧ Real.exp Kernel.d ≤ expDHigh := by
  have hx : |Kernel.d / 2| ≤ (1 : ℝ) := by norm_num [Kernel.d]
  have h := Real.exp_bound (x := Kernel.d / 2) hx (n := 60) (by norm_num)
  norm_num [Kernel.d, Finset.sum_range_succ, Nat.factorial] at h
  have hl : (42345334717148346640792269030148202402250954427462968299639552475273762561886687 / 25000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ Real.exp (Kernel.d / 2) := by
    norm_num [Kernel.d]
    linarith [(abs_le.mp h).1]
  have hh : Real.exp (Kernel.d / 2) ≤ (169381338868593386563169076120592809609003817709851873198558209901095050247546749 / 100000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    norm_num [Kernel.d]
    linarith [(abs_le.mp h).2]
  have he : Real.exp Kernel.d = (Real.exp (Kernel.d / 2)) ^ 2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  constructor
  · calc
      _ ≤ (42345334717148346640792269030148202402250954427462968299639552475273762561886687 / 25000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ^ 2 := by norm_num [expDLow]
      _ ≤ _ := by rw [he]; gcongr
  · calc
      _ ≤ (169381338868593386563169076120592809609003817709851873198558209901095050247546749 / 100000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) ^ 2 := by rw [he]; gcongr
      _ ≤ _ := by norm_num [expDHigh]

#print axioms exp_d_bounds
end Varlamov
