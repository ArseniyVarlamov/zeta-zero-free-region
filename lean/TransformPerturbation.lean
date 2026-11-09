import PrimeNumberTheoremAnd.IEANTN.Varlamov.PairedPositivity
import Mathlib.Tactic.GCongr

namespace Varlamov
noncomputable def T0 : ℝ := 10000000000
lemma T0_pos : 0 < T0 := by norm_num [T0]

namespace Kernel
open Real

/-- Uniform real-translation estimate used in Lemma 5.3. -/
theorem W_real_perturbation {ξ : ℂ} {η E v : ℝ}
    (hη : 0 < η) (hηE : η ≤ E) (hE : E < 1)
    (hξ : 0 ≤ ξ.re) (hv : |v| ≤ η) (hy : T0 ≤ |ξ.im|) :
    ‖W ((ξ + (v : ℂ)) / (η : ℂ)) - W (ξ / (η : ℂ))‖ ≤
      η / ξ.im ^ 2 * (10 + 2 * Cminus * E ^ 2 / T0) := by
  have hy0 : 0 < |ξ.im| := T0_pos.trans_le hy
  have hη0 : η ≠ 0 := ne_of_gt hη
  have hηC : (η : ℂ) ≠ 0 := by exact_mod_cast hη0
  have hE0 : 0 < E := hη.trans_le hηE
  have hCm := Cminus_pos
  let Z0 : ℂ := ξ / (η : ℂ)
  let Z1 : ℂ := (ξ + (v : ℂ)) / (η : ℂ)
  let r : ℝ := |ξ.im| / η
  have hr : 0 < r := div_pos hy0 hη
  have hIm0 : |Z0.im| = r := by simp [Z0, r, abs_div, abs_of_pos hη]
  have hIm1 : |Z1.im| = r := by simp [Z1, r, abs_div, abs_of_pos hη]
  have hn0 : r ≤ ‖Z0‖ := hIm0.symm ▸ Complex.abs_im_le_norm Z0
  have hn1 : r ≤ ‖Z1‖ := hIm1.symm ▸ Complex.abs_im_le_norm Z1
  have hZ0 : Z0 ≠ 0 := norm_pos_iff.mp (hr.trans_le hn0)
  have hZ1 : Z1 ≠ 0 := norm_pos_iff.mp (hr.trans_le hn1)
  have hRe0 : -1 ≤ Z0.re := by
    have hz : 0 ≤ Z0.re := by simp only [Z0, Complex.div_ofReal_re]; exact div_nonneg hξ hη.le
    linarith
  have hRe1 : -1 ≤ Z1.re := by
    simp only [Z1, Complex.div_ofReal_re, Complex.add_re, Complex.ofReal_re]
    apply (le_div_iff₀ hη).mpr
    linarith [(abs_le.mp hv).1]
  have hrem (Z : ℂ) (hZ : Z ≠ 0) (hRe : -1 ≤ Z.re) (hn : r ≤ ‖Z‖) :
      ‖W Z - 10 / Z‖ ≤ Cminus * η ^ 3 / |ξ.im| ^ 3 := by
    have hc : r ^ 3 ≤ ‖Z‖ ^ 3 := by gcongr
    have h := (W_left_bound hZ hRe).trans
      (div_le_div_of_nonneg_left hCm.le (pow_pos hr 3) hc)
    have he : Cminus / r ^ 3 = Cminus * η ^ 3 / |ξ.im| ^ 3 := by dsimp [r]; field_simp
    simpa only [he] using h
  have hrem0 := hrem Z0 hZ0 hRe0 hn0
  have hrem1 := hrem Z1 hZ1 hRe1 hn1
  have hξ0 : ξ ≠ 0 := norm_pos_iff.mp (hy0.trans_le (Complex.abs_im_le_norm ξ))
  have hξv : ξ + (v : ℂ) ≠ 0 := by
    apply norm_pos_iff.mp
    have hb := Complex.abs_im_le_norm (ξ + (v : ℂ))
    simp only [Complex.add_im, Complex.ofReal_im, add_zero] at hb
    exact hy0.trans_le hb
  have hprod : ξ.im ^ 2 ≤ ‖ξ‖ * ‖ξ + (v : ℂ)‖ := by
    have h0 := Complex.abs_im_le_norm ξ
    have h1 := Complex.abs_im_le_norm (ξ + (v : ℂ))
    simp only [Complex.add_im, Complex.ofReal_im, add_zero] at h1
    have hp := mul_le_mul h0 h1 (abs_nonneg ξ.im) (norm_nonneg ξ)
    nlinarith [sq_abs ξ.im]
  have hy2 : 0 < ξ.im ^ 2 := by simpa only [sq_abs] using pow_pos hy0 2
  have hmainEq : (10 : ℂ) / Z1 - 10 / Z0 =
      - (10 * (η : ℂ) * (v : ℂ)) / (ξ * (ξ + (v : ℂ))) := by
    dsimp [Z0, Z1]
    field_simp
    ring
  have hmain : ‖(10 : ℂ) / Z1 - 10 / Z0‖ ≤ 10 * η / ξ.im ^ 2 := by
    rw [hmainEq]
    simp only [norm_div, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hη, show ‖(10 : ℂ)‖ = (10 : ℝ) from by norm_num]
    calc
      _ ≤ 10 * η / (‖ξ‖ * ‖ξ + (v : ℂ)‖) := div_le_div_of_nonneg_right
        (by nlinarith [hv.trans (hηE.trans hE.le)]) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hy2 hprod
  have he : W Z1 - W Z0 = (10 / Z1 - 10 / Z0) + ((W Z1 - 10 / Z1) - (W Z0 - 10 / Z0)) := by ring
  have hsum : ‖W Z1 - W Z0‖ ≤ 10 * η / ξ.im ^ 2 + 2 * Cminus * η ^ 3 / |ξ.im| ^ 3 := by
    calc
      _ ≤ ‖(10 : ℂ) / Z1 - 10 / Z0‖ + ‖(W Z1 - 10 / Z1) - (W Z0 - 10 / Z0)‖ := by
        rw [he]
        exact norm_add_le _ _
      _ ≤ ‖(10 : ℂ) / Z1 - 10 / Z0‖ + (‖W Z1 - 10 / Z1‖ + ‖W Z0 - 10 / Z0‖) :=
        add_le_add le_rfl (norm_sub_le _ _)
      _ ≤ 10 * η / ξ.im ^ 2 + (Cminus * η ^ 3 / |ξ.im| ^ 3 + Cminus * η ^ 3 / |ξ.im| ^ 3) :=
        add_le_add hmain (add_le_add hrem1 hrem0)
      _ = _ := by ring
  have hη2 : η ^ 2 ≤ E ^ 2 := by nlinarith
  have hinner : 2 * Cminus * η ^ 2 / |ξ.im| ≤ 2 * Cminus * E ^ 2 / T0 := by
    calc
      _ ≤ 2 * Cminus * E ^ 2 / |ξ.im| := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hη2 (by positivity)) hy0.le
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) T0_pos hy
  have hmul := mul_le_mul_of_nonneg_left hinner (div_nonneg hη.le (sq_nonneg |ξ.im|))
  apply hsum.trans
  rw [← sq_abs ξ.im]
  calc
    _ = η / |ξ.im| ^ 2 * 10 + η / |ξ.im| ^ 2 * (2 * Cminus * η ^ 2 / |ξ.im|) := by ring
    _ ≤ η / |ξ.im| ^ 2 * 10 + η / |ξ.im| ^ 2 * (2 * Cminus * E ^ 2 / T0) := add_le_add le_rfl hmul
    _ = _ := by ring

#print axioms W_real_perturbation

end Kernel
end Varlamov
