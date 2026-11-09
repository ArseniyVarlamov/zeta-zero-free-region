import PrimeNumberTheoremAnd.IEANTN.Varlamov.LehmanPhi

namespace Varlamov
open Real MeasureTheory
open scoped BigOperators

noncomputable def positivePhiTail (τ T : ℝ) (ρ : NontrivialZeros) : ℝ :=
  if T < (ρ : ℂ).im then phi τ (ρ : ℂ).im * (riemannZeta.order ρ : ℝ) else 0
noncomputable def zeroWindow (f : ℝ → ℝ) (T U : ℝ) (ρ : NontrivialZeros) : ℝ :=
  if T < (ρ : ℂ).im ∧ (ρ : ℂ).im ≤ U then f (ρ : ℂ).im * (riemannZeta.order ρ : ℝ) else 0

/-- Lehman (1966), Lemma 1, p.400, as an absolute error bound on the
multiplicity-weighted window sum. We use a strictly decreasing specialization.
https://doi.org/10.4064/aa-11-4-397-410 . This is a published theorem parameter. -/
def LehmanMonotoneInput : Prop :=
  ∀ T U : ℝ, ∀ f : ℝ → ℝ, 2 * Real.pi * Real.exp 1 ≤ T → T < U →
    ContinuousOn f (Set.Icc T U) → (∀ x ∈ Set.Icc T U, 0 < f x) → StrictAntiOn f (Set.Icc T U) →
    |(∑' ρ : NontrivialZeros, zeroWindow f T U ρ) -
      (1 / (2 * Real.pi)) * (∫ x in T..U, f x * Real.log (x / (2 * Real.pi)))| ≤
      4 * f T * Real.log T + 2 * (∫ x in T..U, f x / x)

lemma phi_strictAntiOn {τ T : ℝ} (hτ : 0 < τ) (hT : τ < T) : StrictAntiOn (phi τ) (Set.Ici T) := by
  intro x hx y hy hxy
  change T ≤ x at hx
  change T ≤ y at hy
  have hm : 0 < x - τ := by linarith [hx]
  have hp : 0 < x + τ := by linarith [hx]
  unfold phi
  gcongr

lemma phi_square_majorant {τ T x : ℝ} (hτ : 0 < τ) (hT : τ < T) (hx : T < x) :
    phi τ x ≤ 2 * (T / (T - τ)) ^ 2 / x ^ 2 := by
  have hx0 : 0 < x := by linarith
  have hm : 0 < x - τ := by linarith
  have hp : 0 < x + τ := by linarith
  have hd : 0 < T - τ := sub_pos.mpr hT
  have ht0 : 0 < T := hτ.trans hT
  have hrat : x / (x - τ) ≤ T / (T - τ) := by
    apply (div_le_div_iff₀ hm hd).mpr
    nlinarith [mul_nonneg hτ.le (show 0 ≤ x - T by linarith)]
  have hrat2 : (x / (x - τ)) ^ 2 ≤ (T / (T - τ)) ^ 2 := by gcongr
  have hplus : 1 / (x + τ) ^ 2 ≤ 1 / (x - τ) ^ 2 := by gcongr; linarith
  have he : 1 / (x - τ) ^ 2 = (x / (x - τ)) ^ 2 / x ^ 2 := by field_simp
  calc
    phi τ x ≤ 2 / (x - τ) ^ 2 := by
      rw [show 2 / (x - τ) ^ 2 = 1 / (x - τ) ^ 2 + 1 / (x - τ) ^ 2 from by ring]
      exact add_le_add le_rfl hplus
    _ = 2 * (x / (x - τ)) ^ 2 / x ^ 2 := by field_simp
    _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hrat2 (by norm_num)) (sq_nonneg x)

lemma positivePhiTail_nonneg (τ T : ℝ) (ρ : NontrivialZeros) : 0 ≤ positivePhiTail τ T ρ := by
  have ho : 0 ≤ (riemannZeta.order ρ : ℝ) := by exact_mod_cast zeta_order_nonneg (nontrivial_ne_one ρ)
  unfold positivePhiTail
  split_ifs
  · exact mul_nonneg (phi_nonneg _ _) ho
  · exact le_rfl

lemma positivePhiTail_summable (hL2 : LehmanSquareTailInput) {τ T : ℝ}
    (hτ : 0 < τ) (hT : τ < T) (hAd : 2 * Real.pi * Real.exp 1 ≤ T) : Summable (positivePhiTail τ T) := by
  let C : ℝ := 2 * (T / (T - τ)) ^ 2
  have hmaj (ρ : NontrivialZeros) : positivePhiTail τ T ρ ≤ C * positiveSquareTail T ρ := by
    have ho : 0 ≤ (riemannZeta.order ρ : ℝ) := by exact_mod_cast zeta_order_nonneg (nontrivial_ne_one ρ)
    by_cases hx : T < (ρ : ℂ).im
    · simp only [positivePhiTail, positiveSquareTail, ite_eq_left hx]
      have h := mul_le_mul_of_nonneg_right (phi_square_majorant hτ hT hx) ho
      convert h using 1 <;> (try dsimp only [C]) <;> ring
    · simp [positivePhiTail, positiveSquareTail, hx]
  exact Summable.of_nonneg_of_le (positivePhiTail_nonneg τ T) hmaj ((hL2 T hAd).1.mul_left C)

lemma phi_window_bound (hL1 : LehmanMonotoneInput) {τ T U : ℝ}
    (hτ : 0 < τ) (hT : τ < T) (hT1 : 1 < T) (hAd : 2 * Real.pi * Real.exp 1 ≤ T) (hTU : T < U) :
    (∑' ρ : NontrivialZeros, zeroWindow (phi τ) T U ρ) ≤
      (1 / (2 * Real.pi)) * (-phiLogPrimitive τ T) + 4 * phi τ T * Real.log T +
        2 * ((1 / (T - τ) + 1 / (T + τ)) / T) := by
  have hc : ContinuousOn (phi τ) (Set.Icc T U) := fun x hx =>
    (phi_continuousAt hτ (hT.trans_le hx.1)).continuousWithinAt
  have hp (x : ℝ) (hx : x ∈ Set.Icc T U) : 0 < phi τ x := by
    have hm : 0 < x - τ := by linarith [hx.1]
    unfold phi
    positivity
  have hs : StrictAntiOn (phi τ) (Set.Icc T U) := (phi_strictAntiOn hτ hT).mono (fun _ hx => hx.1)
  have he := (abs_le.mp (hL1 T U (phi τ) hAd hTU hc hp hs)).2
  have hl := mul_le_mul_of_nonneg_left (phi_log_integral_bound hτ hT hT1 hTU.le)
    (show 0 ≤ 1 / (2 * Real.pi) by positivity)
  have hr := mul_le_mul_of_nonneg_left (phi_ratio_integral_bound hτ hT hTU.le) (show (0 : ℝ) ≤ 2 by norm_num)
  linarith only [he, hl, hr]

/-- The infinite tail bound follows from finite windows. The cutoff used
for a finite set is explicit; no unjustified exchange of limits is used. -/
theorem positivePhiTail_bound (hL1 : LehmanMonotoneInput) (hL2 : LehmanSquareTailInput)
    {τ T : ℝ} (hτ : 0 < τ) (hT : τ < T) (hT1 : 1 < T) (hAd : 2 * Real.pi * Real.exp 1 ≤ T) :
    (∑' ρ : NontrivialZeros, positivePhiTail τ T ρ) ≤
      (1 / (2 * Real.pi)) * (-phiLogPrimitive τ T) + 4 * phi τ T * Real.log T +
        2 * ((1 / (T - τ) + 1 / (T + τ)) / T) := by
  classical
  have hs := positivePhiTail_summable hL2 hτ hT hAd
  apply Real.tsum_le_of_sum_le (positivePhiTail_nonneg τ T)
  intro s
  let U := T + 1 + ∑ ρ ∈ s, |(ρ : ℂ).im|
  have hSum : 0 ≤ ∑ ρ ∈ s, |(ρ : ℂ).im| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hTU : T < U := by dsimp [U]; linarith
  have hw : Summable (zeroWindow (phi τ) T U) := by
    apply (hs.indicator {ρ : NontrivialZeros | (ρ : ℂ).im ≤ U}).congr
    intro ρ
    by_cases h1 : T < (ρ : ℂ).im <;> by_cases h2 : (ρ : ℂ).im ≤ U <;>
      simp [Set.indicator_apply, positivePhiTail, zeroWindow, h1, h2]
  have hn (ρ : NontrivialZeros) : 0 ≤ zeroWindow (phi τ) T U ρ := by
    have ho : 0 ≤ (riemannZeta.order ρ : ℝ) := by exact_mod_cast zeta_order_nonneg (nontrivial_ne_one ρ)
    unfold zeroWindow
    split_ifs
    · exact mul_nonneg (phi_nonneg _ _) ho
    · exact le_rfl
  calc
    _ = ∑ ρ ∈ s, zeroWindow (phi τ) T U ρ := by
      apply Finset.sum_congr rfl
      intro ρ hρ
      have ha : |(ρ : ℂ).im| ≤ ∑ q ∈ s, |(q : ℂ).im| := Finset.single_le_sum (f := fun q : NontrivialZeros => |(q : ℂ).im|) (fun _ _ => abs_nonneg _) hρ
      have hu : (ρ : ℂ).im ≤ U := by dsimp [U]; linarith [le_abs_self (ρ : ℂ).im]
      simp [positivePhiTail, zeroWindow, hu]
    _ ≤ ∑' ρ : NontrivialZeros, zeroWindow (phi τ) T U ρ := Summable.sum_le_tsum _ (fun ρ _ => hn ρ) hw
    _ ≤ _ := phi_window_bound hL1 hτ hT hT1 hAd hTU

#print axioms positivePhiTail_bound
end Varlamov
