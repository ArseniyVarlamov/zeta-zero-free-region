import PrimeNumberTheoremAnd.IEANTN.Varlamov.WeightedLineIntegral
import PrimeNumberTheoremAnd.IEANTN.Varlamov.DigammaBounds

namespace Varlamov.Kernel
open Real Complex

/-- Absolute convergence of the trivial-zero remainder, uniformly controlled
by an ordinary summable rational majorant. -/
theorem zeroSample_norm_summable {η : ℝ} {s : ℂ}
    (hη : 0 < η) (hs : (1 / 2 : ℝ) < s.re) :
    Summable (fun n : ℕ => ‖zeroSample η s n‖) := by
  let P : ℝ := C (s.re / η) * η ^ 3
  have hs0 : 0 < s.re := by linarith
  have hP : 0 < P := mul_pos (C_pos (div_pos hs0 hη)) (pow_pos hη 3)
  have hmaj : Summable (fun n : ℕ => 8 * P / ((n : ℝ) + 1) ^ 2) := by
    simpa only [mul_one_div] using Complex.summable_one_div_natCast_add_one_sq.mul_left (8 * P)
  have hb (n : ℕ) : ‖zeroSample η s n‖ ≤ 8 * P / ((n : ℝ) + 1) ^ 2 := by
    let u : ℂ := s + 2 * (n : ℂ)
    let m : ℝ := (n : ℝ) + 1
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hm : 1 ≤ m := by dsimp [m]; linarith
    have hmp : 0 < m := by linarith
    have hu : s.re ≤ u.re := by simp [u]
    have hlin : m / 2 ≤ ‖u‖ := by
      have hr : m / 2 ≤ u.re := by simp [u, m]; linarith
      exact hr.trans (Complex.re_le_norm u)
    have hc : (m / 2) ^ 3 ≤ ‖u‖ ^ 3 := by gcongr
    have hpow : m ^ 2 / 8 ≤ ‖u‖ ^ 3 := by
      have h := mul_nonneg (sq_nonneg m) (show 0 ≤ m - 1 by linarith)
      nlinarith
    have h := W0_scaled_norm hη hs0 hu
    calc
      ‖zeroSample η s n‖ ≤ P / ‖u‖ ^ 3 := h
      _ ≤ P / (m ^ 2 / 8) := div_le_div_of_nonneg_left hP.le (by positivity) hpow
      _ = _ := by rw [div_div_eq_mul_div]; dsimp [m]; ring
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb hmaj

lemma zeroSample_summable {η : ℝ} {s : ℂ} (hη : 0 < η) (hs : (1 / 2 : ℝ) < s.re) :
    Summable (zeroSample η s) := (zeroSample_norm_summable hη hs).of_norm

#print axioms zeroSample_norm_summable

end Varlamov.Kernel
