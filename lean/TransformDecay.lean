import PrimeNumberTheoremAnd.IEANTN.Varlamov.TransformBounds

namespace Varlamov.Kernel
open Real

lemma C_pos {ν : ℝ} (hν : 0 < ν) : 0 < C ν := by
  unfold C
  have h3 := scaled_third_pos
  have h4 := M4star_pos
  positivity

lemma Cminus_pos : 0 < Cminus := by
  unfold Cminus
  have h3 := scaled_third_pos
  have h4 := M4star_pos
  have hd := d_pos
  positivity

/-- A uniform bound sufficient to pass to infinity in the strip minimum principle. -/
lemma W_norm_large_im {z : ℂ} (hz : 0 ≤ z.re) (hy : 1 ≤ |z.im|) :
    ‖W z‖ ≤ (10 + Cminus) / |z.im| := by
  have hnorm : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z
  have h1 : 1 ≤ ‖z‖ := hy.trans hnorm
  have hz0 : z ≠ 0 := norm_pos_iff.mp (by linarith)
  have hy0 : 0 < |z.im| := by linarith
  have h2 : 1 ≤ ‖z‖ ^ 2 := by nlinarith
  have h3 : ‖z‖ ≤ ‖z‖ ^ 3 := by
    have h := mul_nonneg (norm_nonneg z) (show 0 ≤ ‖z‖ ^ 2 - 1 by linarith)
    nlinarith
  have hr := W_left_bound hz0 (show - 1 ≤ z.re by linarith)
  have he : W z = 10 / z + (W z - 10 / z) := by ring
  calc
    ‖W z‖ ≤ ‖(10 : ℂ) / z‖ + ‖W z - 10 / z‖ := by
      conv_lhs => rw [he]
      exact norm_add_le _ _
    _ ≤ 10 / ‖z‖ + Cminus / ‖z‖ ^ 3 := by
      rw [norm_div, show ‖(10 : ℂ)‖ = (10 : ℝ) from by norm_num]
      exact add_le_add le_rfl hr
    _ ≤ 10 / |z.im| + Cminus / |z.im| :=
      add_le_add (div_le_div_of_nonneg_left (by norm_num) hy0 hnorm)
        (div_le_div_of_nonneg_left Cminus_pos.le hy0 (hnorm.trans h3))
    _ = (10 + Cminus) / |z.im| := by ring

#print axioms W_norm_large_im

end Varlamov.Kernel
