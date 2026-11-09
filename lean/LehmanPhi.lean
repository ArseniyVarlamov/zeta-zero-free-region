import PrimeNumberTheoremAnd.IEANTN.Varlamov.RealZeroTail

namespace Varlamov
open Real MeasureTheory

noncomputable def phi (τ x : ℝ) : ℝ := 1 / (x - τ) ^ 2 + 1 / (x + τ) ^ 2
noncomputable def phiPrimitive (τ x : ℝ) : ℝ := -1 / (x - τ) - 1 / (x + τ)
noncomputable def phiLogUpper (τ x : ℝ) : ℝ := (1 / (x - τ) ^ 2 + 1 / x ^ 2) * Real.log x
noncomputable def phiLogPrimitive (τ x : ℝ) : ℝ :=
  - Real.log x / (x - τ) + (1 / τ) * (Real.log (x - τ) - Real.log x) - (Real.log x + 1) / x

lemma phiPrimitive_hasDerivAt {τ x : ℝ} (hτ : 0 < τ) (hx : τ < x) :
    HasDerivAt (phiPrimitive τ) (phi τ x) x := by
  have hm : x - τ ≠ 0 := ne_of_gt (sub_pos.mpr hx)
  have hp : x + τ ≠ 0 := ne_of_gt (by linarith)
  have h1 := ((hasDerivAt_id x).sub_const τ).inv hm |>.neg
  have h2 := ((hasDerivAt_id x).add_const τ).inv hp |>.neg
  convert h1.add h2 using 1
  · funext y
    dsimp [phiPrimitive]
    ring
  · dsimp [phi]
    field_simp
    <;> ring

lemma phiLogPrimitive_hasDerivAt {τ x : ℝ} (hτ : 0 < τ) (hx : τ < x) :
    HasDerivAt (phiLogPrimitive τ) (phiLogUpper τ x) x := by
  have hx0 : x ≠ 0 := ne_of_gt (by linarith)
  have hm : x - τ ≠ 0 := ne_of_gt (sub_pos.mpr hx)
  have ht0 : τ ≠ 0 := ne_of_gt hτ
  have hl := Real.hasDerivAt_log hx0
  have hml := ((hasDerivAt_id x).sub_const τ).log hm
  have h1 := (hl.div ((hasDerivAt_id x).sub_const τ) hm).neg
  have h2 := (hml.sub hl).const_mul (1 / τ)
  have h3 := ((hl.add_const 1).div (hasDerivAt_id x) hx0).neg
  convert (h1.add h2).add h3 using 1
  · funext y
    dsimp [phiLogPrimitive]
    ring
  · dsimp [phiLogUpper]
    field_simp
    <;> ring

lemma phi_nonneg (τ x : ℝ) : 0 ≤ phi τ x := by unfold phi; positivity

lemma phi_continuousAt {τ x : ℝ} (hτ : 0 < τ) (hx : τ < x) : ContinuousAt (phi τ) x := by
  have hm : (x - τ) ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt (sub_pos.mpr hx))
  have hp : (x + τ) ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt (by linarith))
  exact (continuousAt_const.div ((continuousAt_id.sub_const τ).pow 2) hm).add
    (continuousAt_const.div ((continuousAt_id.add_const τ).pow 2) hp)

lemma phiLogUpper_continuousAt {τ x : ℝ} (hτ : 0 < τ) (hx : τ < x) : ContinuousAt (phiLogUpper τ) x := by
  have hm : (x - τ) ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt (sub_pos.mpr hx))
  have hx0 : x ≠ 0 := ne_of_gt (by linarith)
  exact ((continuousAt_const.div ((continuousAt_id.sub_const τ).pow 2) hm).add
    (continuousAt_const.div (continuousAt_id.pow 2) (pow_ne_zero 2 hx0))).mul
      (Real.continuousAt_log hx0)

lemma phi_antitoneOn {τ T : ℝ} (hτ : 0 < τ) (hT : τ < T) : AntitoneOn (phi τ) (Set.Ici T) := by
  intro x hx y hy hxy
  change T ≤ x at hx
  change T ≤ y at hy
  unfold phi
  have hxm : 0 < x - τ := by linarith [hx]
  have hxp : 0 < x + τ := by linarith [hx]
  gcongr

lemma phiLogPrimitive_nonpos {τ T x : ℝ} (hτ : 0 < τ) (hT : τ < T) (hT1 : 1 < T) (hx : T ≤ x) :
    phiLogPrimitive τ x ≤ 0 := by
  have hx0 : 0 < x := by linarith
  have hm : 0 < x - τ := by linarith
  have hl : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hdiff : Real.log (x - τ) - Real.log x ≤ 0 := by
    have h := Real.log_le_log hm (by linarith : x - τ ≤ x)
    linarith
  unfold phiLogPrimitive
  have h1 : -Real.log x / (x - τ) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hm.le
  have h2 : (1 / τ) * (Real.log (x - τ) - Real.log x) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hdiff
  have h3 : 0 ≤ (Real.log x + 1) / x := by positivity
  linarith

/-- The finite logarithmic integral has a uniform upper bound, avoiding
an improper-integral or Stieltjes formalization in the tail comparison. -/
theorem phi_log_integral_bound {τ T U : ℝ} (hτ : 0 < τ) (hT : τ < T) (hT1 : 1 < T) (hTU : T ≤ U) :
    (∫ x in T..U, phi τ x * Real.log (x / (2 * Real.pi))) ≤ -phiLogPrimitive τ T := by
  have hPhi : ContinuousOn (phi τ) (Set.Icc T U) := fun x hx =>
    (phi_continuousAt hτ (hT.trans_le hx.1)).continuousWithinAt
  have hUpper : ContinuousOn (phiLogUpper τ) (Set.Icc T U) := fun x hx =>
    (phiLogUpper_continuousAt hτ (hT.trans_le hx.1)).continuousWithinAt
  have hLog : ContinuousOn (fun x : ℝ => Real.log (x / (2 * Real.pi))) (Set.Icc T U) := by
    intro x hx
    have hp : 2 * Real.pi ≠ 0 := by positivity
    have hx0 : x / (2 * Real.pi) ≠ 0 := div_ne_zero (ne_of_gt (by linarith [hx.1])) hp
    exact ((continuousAt_id.div_const _).log hx0).continuousWithinAt
  have hi : IntervalIntegrable (fun x : ℝ => phi τ x * Real.log (x / (2 * Real.pi))) volume T U :=
    (hPhi.mul hLog).intervalIntegrable_of_Icc hTU
  have hu : IntervalIntegrable (phiLogUpper τ) volume T U := hUpper.intervalIntegrable_of_Icc hTU
  have hpt (x : ℝ) (hx : x ∈ Set.Icc T U) : phi τ x * Real.log (x / (2 * Real.pi)) ≤ phiLogUpper τ x := by
    have hx0 : 0 < x := by linarith [hx.1]
    have hlog : 0 ≤ Real.log x := Real.log_nonneg (by linarith [hx.1])
    have hpi : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
    have hlogle : Real.log (x / (2 * Real.pi)) ≤ Real.log x := by
      rw [Real.log_div (ne_of_gt hx0) (by positivity)]
      linarith
    have hden : 1 / (x + τ) ^ 2 ≤ 1 / x ^ 2 := by gcongr; linarith
    calc
      _ ≤ phi τ x * Real.log x := mul_le_mul_of_nonneg_left hlogle (phi_nonneg _ _)
      _ ≤ _ := by unfold phi phiLogUpper; gcongr
  have hI := intervalIntegral.integral_mono_on hTU hi hu hpt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => phiLogPrimitive_hasDerivAt hτ (hT.trans_le (Set.uIcc_of_le hTU ▸ hx).1)) hu] at hI
  exact hI.trans (by linarith [phiLogPrimitive_nonpos hτ hT hT1 hTU])

theorem phi_ratio_integral_bound {τ T U : ℝ} (hτ : 0 < τ) (hT : τ < T) (hTU : T ≤ U) :
    (∫ x in T..U, phi τ x / x) ≤ (1 / (T - τ) + 1 / (T + τ)) / T := by
  have hT0 : 0 < T := hτ.trans hT
  have hPhi : ContinuousOn (phi τ) (Set.Icc T U) := fun x hx =>
    (phi_continuousAt hτ (hT.trans_le hx.1)).continuousWithinAt
  have hiP : IntervalIntegrable (phi τ) volume T U := hPhi.intervalIntegrable_of_Icc hTU
  have hRatio : ContinuousOn (fun x : ℝ => phi τ x / x) (Set.Icc T U) := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt (hT0.trans_le hx.1)
    exact ((phi_continuousAt hτ (hT.trans_le hx.1)).div continuousAt_id hx0).continuousWithinAt
  have hiR : IntervalIntegrable (fun x : ℝ => phi τ x / x) volume T U := hRatio.intervalIntegrable_of_Icc hTU
  have hiC := hiP.div_const T
  have hI := intervalIntegral.integral_mono_on hTU hiR hiC (fun x hx =>
    div_le_div_of_nonneg_left (phi_nonneg _ _) hT0 hx.1)
  rw [intervalIntegral.integral_div] at hI
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => phiPrimitive_hasDerivAt hτ (hT.trans_le (Set.uIcc_of_le hTU ▸ hx).1)) hiP
  rw [hFTC] at hI
  have hU : phiPrimitive τ U ≤ 0 := by
    have hm : 0 < U - τ := by linarith
    have hp : 0 < U + τ := by linarith
    have h1 : -1 / (U - τ) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by norm_num) hm.le
    have h2 : 0 ≤ 1 / (U + τ) := by positivity
    unfold phiPrimitive
    linarith
  unfold phiPrimitive at hI
  apply hI.trans
  unfold phiPrimitive at hU
  apply div_le_div_of_nonneg_right _ hT0.le
  ring_nf at hU ⊢
  linarith

#print axioms phi_log_integral_bound
#print axioms phi_ratio_integral_bound
end Varlamov
