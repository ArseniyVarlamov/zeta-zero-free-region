import PrimeNumberTheoremAnd.IEANTN.Varlamov.KernelIntegral
import PrimeNumberTheoremAnd.IEANTN.Varlamov.KernelDerivatives

namespace Varlamov.Kernel
open Real MeasureTheory

noncomputable def w (u : ℝ) : ℝ := if |u| ≤ d then piece |u| else 0
noncomputable def correlation (v : ℝ) : ℝ := ∫ x : ℝ, bump x * bump (x - v)

lemma w_even (u : ℝ) : w (-u) = w u := by simp [w]
lemma w_piece {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) d) : w u = piece u := by
  simp [w, abs_of_nonneg hu.1, hu.2]
lemma w_zero : w 0 = 10 := by simp [w, d_pos.le, piece_at_zero]
lemma w_vanishes {u : ℝ} (hu : d ≤ |u|) : w u = 0 := by
  by_cases he : |u| ≤ d
  · have heq : |u| = d := le_antisymm he hu
    simp [w, he, heq, piece_at_end]
  · simp [w, he]
lemma w_nonneg (u : ℝ) : 0 ≤ w u := by
  unfold w
  split_ifs with hu
  · exact unit_nonneg _ (normalized_mem ⟨abs_nonneg u, hu⟩)
  · exact le_rfl
lemma w_le_ten (u : ℝ) : w u ≤ 10 := by
  unfold w
  split_ifs with hu
  · exact unit_le_ten _ (normalized_mem ⟨abs_nonneg u, hu⟩)
  · norm_num

lemma w_antitone : AntitoneOn w (Set.Ici (0 : ℝ)) := by
  intro u hu v hv huv
  by_cases hvd : v ≤ d
  · have hud : u ≤ d := huv.trans hvd
    rw [w_piece ⟨hu, hud⟩, w_piece ⟨hv, hvd⟩]
    apply unit_antitone (normalized_mem ⟨hu, hud⟩) (normalized_mem ⟨hv, hvd⟩)
    exact div_le_div_of_nonneg_right huv d_pos.le
  · rw [w_vanishes (show d ≤ |v| by rw [abs_of_nonneg hv]; linarith)]
    exact w_nonneg u

lemma correlation_even (v : ℝ) : correlation (-v) = correlation v := by
  have h := MeasureTheory.integral_add_right_eq_self (μ := volume) (fun x => bump x * bump (x - v)) v
  simpa [correlation, sub_neg_eq_add, mul_comm] using h

lemma correlation_vanishes {v : ℝ} (hv : 2 ≤ v) : correlation v = 0 := by
  have hf : (fun x : ℝ => bump x * bump (x - v)) = 0 := by
    funext x
    by_cases hx : 1 ≤ x
    · rw [bump_zero_of_one_le hx, zero_mul]
      rfl
    · rw [bump_zero_of_le_neg_one (show x - v ≤ -1 by linarith), mul_zero]
      rfl
  simp [correlation, hf]

lemma w_eq_autocorrelation_nonneg {u : ℝ} (hu : 0 ≤ u) :
    w u = 10 / qnorm * correlation (2 * u / d) := by
  by_cases hud : u ≤ d
  · rw [w_piece ⟨hu, hud⟩]
    exact piece_eq_autocorrelation ⟨hu, hud⟩
  · rw [w_vanishes (show d ≤ |u| by rw [abs_of_nonneg hu]; linarith),
      correlation_vanishes (show 2 ≤ 2 * u / d by
        apply (le_div_iff₀ d_pos).mpr
        nlinarith)]
    ring

@[blueprint "varlamov-kernel-autocorrelation"
  (title := "Varlamov, kernel construction and support")
  (statement := /-- The explicit compactly supported even kernel equals the normalized
  autocorrelation of q, with $w(0)=10$, $0\le w\le10$, and it decreases for positive u. -/)]
theorem w_eq_autocorrelation (u : ℝ) : w u = 10 / qnorm * correlation (2 * u / d) := by
  rcases le_or_gt 0 u with hu | hu
  · exact w_eq_autocorrelation_nonneg hu
  · calc
      w u = w (-u) := (w_even u).symm
      _ = 10 / qnorm * correlation (2 * (-u) / d) := w_eq_autocorrelation_nonneg (by linarith)
      _ = 10 / qnorm * correlation (-(2 * u / d)) := by congr 2 ; ring
      _ = 10 / qnorm * correlation (2 * u / d) := by rw [correlation_even]

#print axioms w_eq_autocorrelation
#print axioms w_antitone

end Varlamov.Kernel
