import PrimeNumberTheoremAnd.IEANTN.Varlamov.ZeroSymmetry
import PrimeNumberTheoremAnd.IEANTN.Varlamov.TailConstants

namespace Varlamov
open Real
open scoped BigOperators ComplexConjugate

lemma zeta_order_nonneg {z : ℂ} (hz : z ≠ 1) : 0 ≤ riemannZeta.order z := by
  have ha := analyticOn_riemannZeta z (by simpa using hz)
  unfold riemannZeta.order
  rw [ha.meromorphicOrderAt_eq]
  cases ho : analyticOrderAt riemannZeta z with
  | top => simp
  | coe n =>
      simp only [ENat.map_natCast, WithTop.untopD_coe]
      exact_mod_cast Nat.zero_le n

lemma nontrivial_ne_one (ρ : NontrivialZeros) : (ρ : ℂ) ≠ 1 := by
  intro he
  have hr := congrArg Complex.re he
  simp only [Complex.one_re] at hr
  linarith [ρ.property.1.2]

noncomputable def conjugateZero (ρ : NontrivialZeros) : NontrivialZeros :=
  ⟨conj (ρ : ℂ), ⟨by simpa using ρ.property.1, Set.mem_univ _, zeta_eq_zero_conj ρ.property.2.2⟩⟩
lemma conjugateZero_involutive : Function.Involutive conjugateZero := by
  intro ρ
  apply Subtype.ext
  simp [conjugateZero]
noncomputable def conjugateZeroEquiv : NontrivialZeros ≃ NontrivialZeros :=
  { toFun := conjugateZero, invFun := conjugateZero,
    left_inv := conjugateZero_involutive, right_inv := conjugateZero_involutive }
lemma conjugateZero_order (ρ : NontrivialZeros) : riemannZeta.order (conjugateZero ρ) = riemannZeta.order ρ :=
  zeta_order_conj (nontrivial_ne_one ρ)

noncomputable def positiveSquareTail (T : ℝ) (ρ : NontrivialZeros) : ℝ :=
  if T < (ρ : ℂ).im then 1 / (ρ : ℂ).im ^ 2 * (riemannZeta.order ρ : ℝ) else 0
noncomputable def absoluteSquareTail (T : ℝ) (ρ : NontrivialZeros) : ℝ :=
  if T < |(ρ : ℂ).im| then 1 / (ρ : ℂ).im ^ 2 * (riemannZeta.order ρ : ℝ) else 0

/-- Published Lehman (1966), Lemma 2, p.400, specialized to n=2.
https://doi.org/10.4064/aa-11-4-397-410 . Read from the local scanned PDF,
page 3 left. N(T) counts nontrivial zeros with their multiplicities.
This is an ordinary published theorem parameter, not a new axiom. -/
def LehmanSquareTailInput : Prop :=
  ∀ T : ℝ, 2 * Real.pi * Real.exp 1 ≤ T →
    Summable (positiveSquareTail T) ∧ (∑' ρ : NontrivialZeros, positiveSquareTail T ρ) < Real.log T / T

lemma absoluteSquareTail_nonneg (T : ℝ) (ρ : NontrivialZeros) : 0 ≤ absoluteSquareTail T ρ := by
  have ho : 0 ≤ (riemannZeta.order ρ : ℝ) := by exact_mod_cast zeta_order_nonneg (nontrivial_ne_one ρ)
  unfold absoluteSquareTail
  split_ifs <;> positivity

lemma absoluteSquareTail_pair {T : ℝ} (hT : 0 < T) (ρ : NontrivialZeros) :
    absoluteSquareTail T ρ = positiveSquareTail T ρ + positiveSquareTail T (conjugateZero ρ) := by
  have hc : positiveSquareTail T (conjugateZero ρ) =
      if T < -(ρ : ℂ).im then 1 / (-(ρ : ℂ).im) ^ 2 * (riemannZeta.order ρ : ℝ) else 0 := by
    simp only [positiveSquareTail, conjugateZero_order]
    rfl
  rw [hc]
  unfold absoluteSquareTail positiveSquareTail
  by_cases hγ : 0 ≤ (ρ : ℂ).im
  · have hn : ¬T < -(ρ : ℂ).im := by linarith
    simp only [abs_of_nonneg hγ, ite_eq_right hn, add_zero]
  · have hn : ¬T < (ρ : ℂ).im := by linarith
    simp only [abs_of_neg (lt_of_not_ge hγ), ite_eq_right hn, zero_add, neg_sq]

lemma T0_Lehman_admissible : 2 * Real.pi * Real.exp 1 ≤ T0 := by
  have hp := Real.pi_lt_four
  have he := Real.exp_one_lt_three
  have hpe : Real.pi * Real.exp 1 < (4 : ℝ) * 3 :=
    (mul_lt_mul_of_pos_right hp (Real.exp_pos 1)).trans (mul_lt_mul_of_pos_left he (by norm_num))
  norm_num [T0]
  nlinarith

lemma absoluteSquareTail_bound (hL2 : LehmanSquareTailInput) :
    Summable (absoluteSquareTail T0) ∧
      (∑' ρ : NontrivialZeros, absoluteSquareTail T0 ρ) < 2 * Real.log T0 / T0 := by
  have hT : (0 : ℝ) < T0 := by norm_num [T0]
  have hf := hL2 T0 T0_Lehman_admissible
  have hfc : Summable (fun ρ : NontrivialZeros => positiveSquareTail T0 (conjugateZero ρ)) :=
    conjugateZeroEquiv.summable_iff.mpr hf.1
  have hs : Summable (absoluteSquareTail T0) :=
    (hf.1.add hfc).congr (fun ρ => (absoluteSquareTail_pair hT ρ).symm)
  have he : (∑' ρ : NontrivialZeros, absoluteSquareTail T0 ρ) =
      2 * (∑' ρ : NontrivialZeros, positiveSquareTail T0 ρ) := by
    simp_rw [absoluteSquareTail_pair hT]
    have ha : (∑' ρ : NontrivialZeros, (positiveSquareTail T0 ρ + positiveSquareTail T0 (conjugateZero ρ))) =
        (∑' ρ : NontrivialZeros, positiveSquareTail T0 ρ) +
          (∑' ρ : NontrivialZeros, positiveSquareTail T0 (conjugateZero ρ)) := hf.1.tsum_add hfc
    have hreindex : (∑' ρ : NontrivialZeros, positiveSquareTail T0 (conjugateZero ρ)) =
        ∑' ρ : NontrivialZeros, positiveSquareTail T0 ρ := conjugateZeroEquiv.tsum_eq (positiveSquareTail T0)
    rw [ha, hreindex]
    ring
  refine ⟨hs, ?_⟩
  rw [he]
  calc
    _ < 2 * (Real.log T0 / T0) := mul_lt_mul_of_pos_left hf.2 (by norm_num)
    _ = _ := by ring

@[blueprint "varlamov-real-zero-tail"
  (title := "Varlamov, Lemma 7.1: the zero-frequency case")
  (statement := /-- The real-frequency zero sum is at least $-Z_0$.
  The published Lehman square-tail bound is explicit. Localization,
  multiplicity-preserving conjugation, summability, paired positivity,
  off-strip estimates and all cutoff comparisons are proved here. -/)
  (uses := ["varlamov-zero-reflection-order", "varlamov-zero-localization",
    "varlamov-paired-positivity", "varlamov-off-strip", "varlamov-tail-constants"])]
theorem real_zero_sum_lower_bound (hK2 : KadiriExplicitInput) (hL2 : LehmanSquareTailInput)
    (hPT : PlattTrudgianInput) (j : Fin 7) {σ η A T : ℝ}
    (hA : 0 < A) (hmin : ∀ z : ℂ, Admissible z → A ≤ depth z)
    (hσdef : σ = 1 - A / Real.log T) (hσhalf : (1 / 2 : ℝ) < σ) (hσ1 : σ < 1)
    (hh : hMin j ≤ 2 * σ - 1) (hσeta : 1 - η ≤ σ) (hη : 0 < η) (hηmax : η ≤ etaMax j)
    (hT : T0 ≤ T) :
    - zeroTailReal j ≤ riemannZeta.zeroes_sum (Set.Ioo 0 1) Set.univ (fun ρ => (F j (2 * σ - 1) η ((σ : ℂ) - ρ)).re) := by
  have hh0 : 0 ≤ 2 * σ - 1 := (hMin_pos j).le.trans hh
  have hhi : 2 * σ - 1 < 1 := by linarith
  have hhI : 2 * σ - 1 ∈ Set.Ico (hMin j) 1 := ⟨hh, hhi⟩
  have hS : 0 ≤ S j := by
    unfold S
    have hc := Kernel.Cminus_pos
    have hn := Multiplier.coeffNorm_nonneg j
    have ht : (0 : ℝ) < T0 := by norm_num [T0]
    positivity
  have hTail := absoluteSquareTail_bound hL2
  have hPi : Summable (fun ρ : NontrivialZeros => Pi j (2 * σ - 1) η ((σ : ℂ) - ρ) * (riemannZeta.order ρ : ℝ)) :=
    paired_zero_sum_summable hK2 j hh0 hη (by simpa using hσhalf) (by simp)
  have hpoint (ρ : NontrivialZeros) : (-S j * η) * absoluteSquareTail T0 ρ ≤
      Pi j (2 * σ - 1) η ((σ : ℂ) - ρ) * (riemannZeta.order ρ : ℝ) := by
    have ho : 0 ≤ (riemannZeta.order ρ : ℝ) := by exact_mod_cast zeta_order_nonneg (nontrivial_ne_one ρ)
    by_cases hcut : |(ρ : ℂ).im| ≤ T
    · have hl := zeros_below_cutoff hPT hA hmin (by rw [←hσdef]; exact hσhalf)
        ρ.property.2.2 ρ.property.1.1 ρ.property.1.2 hcut
      rw [←hσdef] at hl
      have hx : ((σ : ℂ) - (ρ : ℂ)).re ∈ Set.Icc (0 : ℝ) (2 * σ - 1) := by
        simp only [Complex.sub_re, Complex.ofReal_re]
        constructor <;> linarith [hl.1, hl.2]
      have hp := mul_nonneg (paired_positivity j hhI hη hηmax hx) ho
      have hn := mul_nonpos_of_nonpos_of_nonneg (show - S j * η ≤ 0 by nlinarith) (absoluteSquareTail_nonneg T0 ρ)
      exact hn.trans hp
    · have hγ : T0 < |(ρ : ℂ).im| := hT.trans_lt (lt_of_not_ge hcut)
      have hx : ((σ : ℂ) - (ρ : ℂ)).re ∈ Set.Icc (-η) ((2 * σ - 1) + η) := by
        simp only [Complex.sub_re, Complex.ofReal_re]
        constructor <;> linarith [ρ.property.1.1, ρ.property.1.2]
      have hy : T0 ≤ |((σ : ℂ) - (ρ : ℂ)).im| := by simpa using hγ.le
      have hp := mul_le_mul_of_nonneg_right (off_strip_bound j hhI hη hηmax hx hy) ho
      simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, neg_sq] at hp
      rw [absoluteSquareTail, ite_eq_left hγ]
      convert hp using 1 <;> ring
  have hsum := (hTail.1.mul_left (-S j * η)).tsum_le_tsum hpoint hPi
  rw [tsum_mul_left] at hsum
  have hc : -S j * η ≤ 0 := by nlinarith
  have hlo := mul_le_mul_of_nonpos_left hTail.2.le hc
  have hfinal := hlo.trans hsum
  have hpair := zeroes_sum_pairing hK2 j (s := (σ : ℂ)) hh0 hη (by simpa using hσhalf) (by simp)
  have hPeq : (1 / 2 : ℝ) * (∑' ρ : NontrivialZeros, Pi j (2 * σ - 1) η ((σ : ℂ) - ρ) * (riemannZeta.order ρ : ℝ)) =
      riemannZeta.zeroes_sum (Set.Ioo 0 1) Set.univ (fun ρ => (F j (2 * σ - 1) η ((σ : ℂ) - ρ)).re) := hpair.symm
  have hL : 0 ≤ Real.log T0 / T0 := div_nonneg log_cutoff_bounds.1.le (by norm_num [T0])
  have hM := mul_le_mul_of_nonneg_left hηmax (mul_nonneg hS hL)
  have hB : 0 ≤ S j * etaMax j * (Real.log T0 / T0) := by
    exact mul_nonneg (mul_nonneg hS (etaMax_range j).1.le) hL
  have hhfinal := mul_le_mul_of_nonneg_left hfinal (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [hPeq] at hhfinal
  have hFloss : -(S j * η * (Real.log T0 / T0)) ≤
      riemannZeta.zeroes_sum (Set.Ioo 0 1) Set.univ (fun ρ => (F j (2 * σ - 1) η ((σ : ℂ) - ρ)).re) := by
    convert hhfinal using 1 <;> ring
  have hM' : -(S j * etaMax j * (Real.log T0 / T0)) ≤ -(S j * η * (Real.log T0 / T0)) := by
    convert neg_le_neg hM using 1 <;> ring
  calc
    - zeroTailReal j = -2 * (S j * etaMax j * (Real.log T0 / T0)) := by unfold zeroTailReal; ring
    _ ≤ -(S j * etaMax j * (Real.log T0 / T0)) := by linarith
    _ ≤ _ := hM'
    _ ≤ _ := hFloss

#print axioms real_zero_sum_lower_bound
end Varlamov
