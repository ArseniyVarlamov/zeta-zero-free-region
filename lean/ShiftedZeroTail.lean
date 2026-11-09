import PrimeNumberTheoremAnd.IEANTN.Varlamov.LehmanDensity

namespace Varlamov
open Real
open scoped BigOperators

lemma log_T0_gt_four : (4 : ℝ) < Real.log T0 := by unfold T0; interval_decide (trust := kernel)

lemma log_cutoff_le_log_height_plus_three {t : ℝ} (ht : H ≤ t) :
    Real.log (12 * t + T0) ≤ Real.log t + 3 := by
  have hH : (0 : ℝ) < H := by norm_num [H]
  have ht0 : 0 < t := hH.trans_le ht
  have hT : (0 : ℝ) < T0 := by norm_num [T0]
  have hm := mul_le_mul_of_nonneg_left ht (div_nonneg hT.le hH.le)
  have he : T0 / H * H = T0 := by field_simp
  rw [he] at hm
  have hf : (0 : ℝ) < 12 + T0 / H := by positivity
  have hbound : 12 * t + T0 ≤ (12 + T0 / H) * t := by nlinarith
  have hl := Real.log_le_log (by positivity : (0 : ℝ) < 12 * t + T0) hbound
  rw [Real.log_mul (ne_of_gt hf) (ne_of_gt ht0)] at hl
  have hLam := lambdaTwo_bounds.2
  unfold lambdaTwo at hLam
  linarith

/-- A coarse tail bound fits the factor-two slack deliberately present in Z_+.
It avoids the sharper logarithmic antiderivative comparison in the manuscript. -/
theorem uniform_positivePhiTail_bound (hL1 : LehmanMonotoneInput) (hL2 : LehmanSquareTailInput)
    {τ T L : ℝ} (hτH : H ≤ τ) (hgap : T0 ≤ T - τ) (hLog : Real.log T ≤ L + 3) (hL : 28 ≤ L) :
    Summable (positivePhiTail τ T) ∧ (∑' ρ : NontrivialZeros, positivePhiTail τ T ρ) ≤ L / (4 * T0) := by
  have hH : (0 : ℝ) < H := by norm_num [H]
  have hT0 : (0 : ℝ) < T0 := by norm_num [T0]
  have hτ : 0 < τ := hH.trans_le hτH
  have hT : τ < T := by linarith
  have hTH : H ≤ T := by linarith
  have hTT0 : T0 ≤ T := by linarith
  have hT1 : 1 < T := by norm_num [H] at hTH; linarith
  have hTpos : 0 < T := by linarith
  have hδ : 0 < T - τ := by linarith
  have hL0 : 0 < L := by linarith
  have hlog0 : 0 ≤ Real.log T := Real.log_nonneg hT1.le
  have hDiff0 : 0 ≤ Real.log T - Real.log (T - τ) := by
    have h := Real.log_le_log hδ (by linarith : T - τ ≤ T)
    linarith
  have hDiff : Real.log T - Real.log (T - τ) ≤ L := by
    have h := Real.log_le_log hT0 hgap
    linarith [log_T0_gt_four]
  have hAd := T0_Lehman_admissible.trans hTT0
  have hF : -phiLogPrimitive τ T ≤ (L + 3) / T0 + L / H + (L + 4) / H := by
    have h1 : Real.log T / (T - τ) ≤ (L + 3) / T0 := div_le_div₀ (by linarith) hLog hT0 hgap
    have h2 : (Real.log T - Real.log (T - τ)) / τ ≤ L / H := div_le_div₀ hL0.le hDiff hH hτH
    have h3 : (Real.log T + 1) / T ≤ (L + 4) / H := div_le_div₀ (by linarith) (by linarith) hH hTH
    have he : -phiLogPrimitive τ T = Real.log T / (T - τ) + (Real.log T - Real.log (T - τ)) / τ + (Real.log T + 1) / T := by
      unfold phiLogPrimitive
      ring
    rw [he]
    linarith only [h1, h2, h3]
  have hF0 : 0 ≤ -phiLogPrimitive τ T := neg_nonneg.mpr (phiLogPrimitive_nonpos hτ hT hT1 le_rfl)
  have hpi : 1 / (2 * Real.pi) ≤ (1 / 6 : ℝ) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    linarith [Real.pi_gt_three]
  have h1 := (mul_le_mul_of_nonneg_right hpi hF0).trans
    (mul_le_mul_of_nonneg_left hF (by norm_num : (0 : ℝ) ≤ 1 / 6))
  have hPhi : phi τ T ≤ 2 / T0 ^ 2 := by
    unfold phi
    calc
      _ ≤ 1 / T0 ^ 2 + 1 / T0 ^ 2 := by gcongr <;> linarith
      _ = _ := by ring
  have h2 : 4 * phi τ T * Real.log T ≤ 8 * (L + 3) / T0 ^ 2 := by
    calc
      _ ≤ 4 * (2 / T0 ^ 2) * (L + 3) := by gcongr
      _ = _ := by ring
  have ha : (1 / (T - τ) + 1 / (T + τ)) / T ≤ 2 / (H * T0) := by
    calc
      _ ≤ (1 / T0 + 1 / T0) / H := by gcongr <;> linarith
      _ = _ := by ring
  have h3 : 2 * ((1 / (T - τ) + 1 / (T + τ)) / T) ≤ 4 / (H * T0) := by
    calc
      _ ≤ 2 * (2 / (H * T0)) := mul_le_mul_of_nonneg_left ha (by norm_num)
      _ = _ := by ring
  refine ⟨positivePhiTail_summable hL2 hτ hT hAd, ?_⟩
  calc
    _ ≤ (1 / (2 * Real.pi)) * (-phiLogPrimitive τ T) + 4 * phi τ T * Real.log T +
        2 * ((1 / (T - τ) + 1 / (T + τ)) / T) := positivePhiTail_bound hL1 hL2 hτ hT hT1 hAd
    _ ≤ (1 / 6 : ℝ) * ((L + 3) / T0 + L / H + (L + 4) / H) + 8 * (L + 3) / T0 ^ 2 + 4 / (H * T0) := by linarith only [h1,h2,h3]
    _ ≤ _ := by norm_num [H, T0]; linarith

noncomputable def shiftedSquareTail (τ T : ℝ) (ρ : NontrivialZeros) : ℝ :=
  if T < |(ρ : ℂ).im| then 1 / (τ - (ρ : ℂ).im) ^ 2 * (riemannZeta.order ρ : ℝ) else 0

lemma shiftedSquareTail_nonneg (τ T : ℝ) (ρ : NontrivialZeros) : 0 ≤ shiftedSquareTail τ T ρ := by
  have ho : 0 ≤ (riemannZeta.order ρ : ℝ) := by exact_mod_cast zeta_order_nonneg (nontrivial_ne_one ρ)
  unfold shiftedSquareTail
  split_ifs <;> positivity

lemma phi_eq_shifted (τ x : ℝ) : phi τ x = 1 / (τ - x) ^ 2 + 1 / (τ + x) ^ 2 := by
  unfold phi
  have he : (x - τ) ^ 2 = (τ - x) ^ 2 := by ring
  rw [he, add_comm x τ]

lemma phi_even (τ x : ℝ) : phi τ (-x) = phi τ x := by
  unfold phi
  have h1 : (-x - τ) ^ 2 = (x + τ) ^ 2 := by ring
  have h2 : (-x + τ) ^ 2 = (x - τ) ^ 2 := by ring
  rw [h1,h2]
  ring

set_option maxHeartbeats 1000000 in
-- The proof normalizes both rational summands in every sign and cutoff case.
lemma shiftedSquareTail_pair {τ T : ℝ} (hT : 0 < T) (ρ : NontrivialZeros) :
    shiftedSquareTail τ T ρ + shiftedSquareTail τ T (conjugateZero ρ) =
      positivePhiTail τ T ρ + positivePhiTail τ T (conjugateZero ρ) := by
  have hc1 : shiftedSquareTail τ T (conjugateZero ρ) =
      if T < |(ρ : ℂ).im| then 1 / (τ + (ρ : ℂ).im) ^ 2 * (riemannZeta.order ρ : ℝ) else 0 := by
    simp only [shiftedSquareTail, conjugateZero_order]
    simp [conjugateZero, abs_neg, sub_neg_eq_add]
  have hc2 : positivePhiTail τ T (conjugateZero ρ) =
      if T < -(ρ : ℂ).im then phi τ (-(ρ : ℂ).im) * (riemannZeta.order ρ : ℝ) else 0 := by
    simp only [positivePhiTail, conjugateZero_order]
    rfl
  rw [hc1,hc2]
  unfold shiftedSquareTail positivePhiTail
  by_cases hγ : 0 ≤ (ρ : ℂ).im
  · have hn : ¬T < -(ρ : ℂ).im := by linarith
    simp only [abs_of_nonneg hγ, ite_eq_right hn, add_zero]
    split_ifs <;> (try simp only [phi_even,phi_eq_shifted]) <;> ring
  · have hn : ¬T < (ρ : ℂ).im := by linarith
    simp only [abs_of_neg (lt_of_not_ge hγ), ite_eq_right hn, zero_add]
    split_ifs <;> (try simp only [phi_even,phi_eq_shifted]) <;> ring

set_option maxHeartbeats 1000000 in
-- Reindexing two nested unconditional series elaborates several function equalities.
/-- Exact conversion of the two-sided shifted tail into the positive-ordinate
phi tail, with multiplicities and absolute convergence. -/
theorem shiftedSquareTail_eq_phi (hL2 : LehmanSquareTailInput) {τ T : ℝ}
    (hτ : 0 < τ) (hT : τ < T) (hAd : 2 * Real.pi * Real.exp 1 ≤ T) :
    Summable (shiftedSquareTail τ T) ∧
      (∑' ρ : NontrivialZeros, shiftedSquareTail τ T ρ) = ∑' ρ : NontrivialZeros, positivePhiTail τ T ρ := by
  have hT0 : 0 < T := hτ.trans hT
  let f := positivePhiTail τ T
  let g := shiftedSquareTail τ T
  have hf : Summable f := positivePhiTail_summable hL2 hτ hT hAd
  have hfc : Summable (fun ρ : NontrivialZeros => f (conjugateZero ρ)) := conjugateZeroEquiv.summable_iff.mpr hf
  have hmaj (ρ : NontrivialZeros) : g ρ ≤ f ρ + f (conjugateZero ρ) := by
    have hp := shiftedSquareTail_pair (τ := τ) hT0 ρ
    have hn := shiftedSquareTail_nonneg τ T (conjugateZero ρ)
    dsimp only [f,g]
    calc
      _ ≤ shiftedSquareTail τ T ρ + shiftedSquareTail τ T (conjugateZero ρ) := le_add_of_nonneg_right hn
      _ = _ := hp
  have hg : Summable g := Summable.of_nonneg_of_le (shiftedSquareTail_nonneg τ T) hmaj (hf.add hfc)
  have hgc : Summable (fun ρ : NontrivialZeros => g (conjugateZero ρ)) := conjugateZeroEquiv.summable_iff.mpr hg
  have he : (∑' ρ : NontrivialZeros, (g ρ + g (conjugateZero ρ))) =
      (∑' ρ : NontrivialZeros, (f ρ + f (conjugateZero ρ))) :=
    tsum_congr (fun ρ => shiftedSquareTail_pair (τ := τ) hT0 ρ)
  have hgadd : (∑' ρ : NontrivialZeros, (g ρ + g (conjugateZero ρ))) =
      (∑' ρ : NontrivialZeros, g ρ) + (∑' ρ : NontrivialZeros, g (conjugateZero ρ)) := hg.tsum_add hgc
  have hfadd : (∑' ρ : NontrivialZeros, (f ρ + f (conjugateZero ρ))) =
      (∑' ρ : NontrivialZeros, f ρ) + (∑' ρ : NontrivialZeros, f (conjugateZero ρ)) := hf.tsum_add hfc
  have hgr : (∑' ρ : NontrivialZeros, g (conjugateZero ρ)) = ∑' ρ : NontrivialZeros, g ρ := conjugateZeroEquiv.tsum_eq g
  have hfr : (∑' ρ : NontrivialZeros, f (conjugateZero ρ)) = ∑' ρ : NontrivialZeros, f ρ := conjugateZeroEquiv.tsum_eq f
  rw [hgadd,hfadd,hgr,hfr] at he
  rw [←two_mul,←two_mul] at he
  have hEq : (∑' ρ : NontrivialZeros, g ρ) = ∑' ρ : NontrivialZeros, f ρ :=
    mul_left_cancel₀ (by norm_num : (2 : ℝ) ≠ 0) he
  exact ⟨hg,hEq⟩

#print axioms uniform_positivePhiTail_bound
#print axioms shiftedSquareTail_eq_phi
end Varlamov
