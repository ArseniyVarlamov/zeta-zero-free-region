import PrimeNumberTheoremAnd.IEANTN.Varlamov.PoleTerms
import PrimeNumberTheoremAnd.IEANTN.Varlamov.RemainderLedger

namespace Varlamov
open Real

noncomputable def lambdaOne : ℝ := Real.log ((12 + T0 / H) / (2 * Real.pi))
noncomputable def lambdaTwo : ℝ := Real.log (12 + T0 / H)
noncomputable def lambdaThree : ℝ :=
  Real.log ((H + T0) / (2 * Real.pi)) / (2 * H + T0) + Real.log ((2 * H + T0) / T0) / H
noncomputable def zeroTailReal (j : Fin 7) : ℝ := 2 * S j * etaMax j * Real.log T0 / T0
noncomputable def zeroTailNonreal (j : Fin 7) : ℝ := S j * Astar * (
  (1 + lambdaOne / Real.log H) / (2 * Real.pi * T0) + lambdaThree / (2 * Real.pi * Real.log H) +
  8 * (1 + lambdaTwo / Real.log H) / T0 ^ 2 + 4 / (H * T0 * Real.log H))
noncomputable def zeroTailBudget (j : Fin 7) : ℝ := zeroTailReal j + aPlus * zeroTailNonreal j

lemma log_height_bounds : (28 : ℝ) < Real.log H ∧ Real.log H < 30 := by
  norm_num [H]
  constructor <;> interval_decide (trust := kernel)
lemma log_cutoff_bounds : (0 : ℝ) < Real.log T0 ∧ Real.log T0 < 24 := by
  norm_num [T0]
  constructor <;> interval_decide (trust := kernel)
lemma lambdaTwo_bounds : 0 < lambdaTwo ∧ lambdaTwo < 3 := by
  norm_num [lambdaTwo, H, T0]
  constructor <;> interval_decide (trust := kernel)

lemma lambdaOne_bounds : 0 < lambdaOne ∧ lambdaOne < 3 := by
  have hπ := Real.pi_pos
  have hπ3 := Real.pi_gt_three
  have hπ4 := Real.pi_lt_four
  have hq : (1 : ℝ) < (12 + T0 / H) / (2 * Real.pi) := by
    apply (lt_div_iff₀ (by positivity)).mpr
    norm_num [T0, H]
    linarith
  have hden : (1 : ℝ) ≤ 2 * Real.pi := by linarith
  have harg : (12 + T0 / H) / (2 * Real.pi) ≤ 12 + T0 / H := by
    apply (div_le_iff₀ (by positivity)).mpr
    have hp : 0 < 12 + T0 / H := by norm_num [T0, H]
    nlinarith
  refine ⟨Real.log_pos hq, ?_⟩
  apply lt_of_le_of_lt (Real.log_le_log (by linarith : (0 : ℝ) < (12 + T0 / H) / (2 * Real.pi)) harg)
  exact lambdaTwo_bounds.2

lemma lambdaThree_bounds : 0 < lambdaThree ∧ lambdaThree < 1e-11 := by
  have hπ := Real.pi_pos
  have hπ3 := Real.pi_gt_three
  have hπ4 := Real.pi_lt_four
  have harg : (1 : ℝ) < (H + T0) / (2 * Real.pi) := by
    apply (lt_div_iff₀ (by positivity)).mpr
    norm_num [H, T0]
    linarith
  have harg' : (H + T0) / (2 * Real.pi) ≤ H + T0 := by
    apply (div_le_iff₀ (by positivity)).mpr
    norm_num [H, T0]
    linarith
  have hlog1 : 0 < Real.log ((H + T0) / (2 * Real.pi)) := Real.log_pos harg
  have hlog2 : 0 < Real.log ((2 * H + T0) / T0) := Real.log_pos (by norm_num [H, T0])
  have hu1 : Real.log ((H + T0) / (2 * Real.pi)) < 30 := by
    apply lt_of_le_of_lt (Real.log_le_log (by linarith : (0 : ℝ) < (H + T0) / (2 * Real.pi)) harg')
    norm_num [H, T0]
    interval_decide (trust := kernel)
  have hu2 : Real.log ((2 * H + T0) / T0) < 7 := by
    norm_num [H, T0]
    interval_decide (trust := kernel)
  unfold lambdaThree
  constructor
  · have hH : (0 : ℝ) < H := by norm_num [H]
    have hT : (0 : ℝ) < T0 := by norm_num [T0]
    positivity
  · have h1 : Real.log ((H + T0) / (2 * Real.pi)) / (2 * H + T0) ≤ 30 / (2 * H + T0) :=
      div_le_div_of_nonneg_right hu1.le (by norm_num [H, T0])
    have h2 : Real.log ((2 * H + T0) / T0) / H ≤ 7 / H :=
      div_le_div_of_nonneg_right hu2.le (by norm_num [H])
    have hc : (30 : ℝ) / (2 * H + T0) + 7 / H < 1e-11 := by norm_num [H, T0]
    linarith

lemma S_upper (j : Fin 7) : S j < 201 := by
  have hn := (coeffNorm_upper j).le
  have he := (etaMax_range j).2.le
  have he0 := (etaMax_range j).1
  have hc := Cminus_upper.le
  have hc0 := Kernel.Cminus_pos
  have hT : (0 : ℝ) < T0 := by norm_num [T0]
  calc
    S j ≤ 2 * 10 * (10 + 2 * 1000000 * (0.01 : ℝ) ^ 2 / T0) := by unfold S; gcongr
    _ < _ := by norm_num [T0]

@[blueprint "varlamov-tail-constants"
  (title := "Varlamov, C7: exact zero-tail budget constants")
  (statement := /-- For every band, the actual article constants Z_0 and
  Z_+ are below $10^{-8}$. This is a certificate of the constants, not yet
  the analytic Lehman-tail estimate for the zero sum. -/)
  (uses := ["varlamov-off-strip"])]
theorem tail_constants_small (j : Fin 7) : zeroTailReal j < 1e-8 ∧ zeroTailNonreal j < 1e-8 := by
  have hπ := Real.pi_gt_three
  have hπ0 := Real.pi_pos
  have hlog := log_height_bounds.1
  have hL0 : 0 < Real.log H := by linarith
  have hT : (0 : ℝ) < T0 := by norm_num [T0]
  have hH : (0 : ℝ) < H := by norm_num [H]
  have hS := S_upper j
  have hS0 : 0 ≤ S j := by
    unfold S
    have hc := Kernel.Cminus_pos
    have hn := Multiplier.coeffNorm_nonneg j
    positivity
  have he := (etaMax_range j).2
  have he0 := (etaMax_range j).1
  obtain ⟨hLam10, hLam13⟩ := lambdaOne_bounds
  obtain ⟨hLam20, hLam23⟩ := lambdaTwo_bounds
  obtain ⟨hLam30, hLam3u⟩ := lambdaThree_bounds
  have hA : Astar < (0.21 : ℝ) := by norm_num [Astar]
  have hA0 := Astar_pos
  constructor
  · calc
      zeroTailReal j ≤ 2 * 201 * (0.01 : ℝ) * 24 / T0 := by
        unfold zeroTailReal
        gcongr
        exact log_cutoff_bounds.1.le
        exact log_cutoff_bounds.2.le
      _ < _ := by norm_num [T0]
  · calc
      zeroTailNonreal j ≤ 201 * (0.21 : ℝ) * (
          (1 + 3 / (28 : ℝ)) / (2 * 3 * T0) + (1e-11 : ℝ) / (2 * 3 * 28) +
          8 * (1 + 3 / (28 : ℝ)) / T0 ^ 2 + 4 / (H * T0 * 28)) := by
        unfold zeroTailNonreal
        gcongr <;> positivity
      _ < _ := by norm_num [H, T0]

#print axioms tail_constants_small
end Varlamov
