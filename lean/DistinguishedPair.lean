import PrimeNumberTheoremAnd.IEANTN.Varlamov.RealZeroTail
import PrimeNumberTheoremAnd.IEANTN.Varlamov.Ledger

namespace Varlamov
open Real
open scoped BigOperators ComplexConjugate

/-- A genuine nontrivial zero has positive finite multiplicity. -/
theorem nontrivial_order_pos (ρ : NontrivialZeros) : (1 : ℤ) ≤ riemannZeta.order ρ := by
  have hne := nontrivial_ne_one ρ
  have ha : AnalyticAt ℂ riemannZeta (ρ : ℂ) := analyticOn_riemannZeta _ (by simpa using hne)
  have ha2 : AnalyticAt ℂ riemannZeta (2 : ℂ) := analyticOn_riemannZeta _ (by simp)
  have h2 : analyticOrderAt riemannZeta (2 : ℂ) = 0 :=
    ha2.analyticOrderAt_eq_zero.mpr (riemannZeta_ne_zero_of_one_le_re (by norm_num))
  have hconn : IsPreconnected (({1} : Set ℂ)ᶜ) :=
    (isConnected_compl_singleton_of_one_lt_rank (by simp) (1 : ℂ)).isPreconnected
  have htop := analyticOn_riemannZeta.analyticOrderAt_ne_top_of_isPreconnected hconn
    (x := (2 : ℂ)) (y := (ρ : ℂ)) (by simp) (by simpa using hne) (by simp [h2])
  have hzero : analyticOrderAt riemannZeta (ρ : ℂ) ≠ 0 := ha.analyticOrderAt_ne_zero.mpr ρ.property.2.2
  unfold riemannZeta.order
  rw [ha.meromorphicOrderAt_eq]
  cases ho : analyticOrderAt riemannZeta (ρ : ℂ) with
  | top => exact False.elim (htop ho)
  | coe n =>
      have hn : n ≠ 0 := by intro hz; apply hzero; simp [ho, hz]
      simp only [ENat.map_natCast, WithTop.untopD_coe]
      exact_mod_cast (show 1 ≤ n from Nat.one_le_iff_ne_zero.mpr hn)

noncomputable def lowPairedTerm (j : Fin 7) (σ η τ T : ℝ) (ρ : NontrivialZeros) : ℝ :=
  if |(ρ : ℂ).im| ≤ T then Pi j (2 * σ - 1) η (((σ : ℂ) + (τ : ℂ) * Complex.I) - ρ) * (riemannZeta.order ρ : ℝ) else 0
noncomputable def mainPairValue (j : Fin 7) (σ η : ℝ) : ℝ :=
  (F j (2 * σ - 1) η (((σ - 1 + η : ℝ)) : ℂ)).re + (F j (2 * σ - 1) η (((σ - η : ℝ)) : ℂ)).re

lemma Pi_low_zero_nonneg (hPT : PlattTrudgianInput) (j : Fin 7) {σ η τ A T : ℝ}
    (hA : 0 < A) (hmin : ∀ z : ℂ, Admissible z → A ≤ depth z)
    (hσdef : σ = 1 - A / Real.log T) (hσhalf : (1 / 2 : ℝ) < σ) (hσ1 : σ < 1)
    (hh : hMin j ≤ 2 * σ - 1) (hη : 0 < η) (hηmax : η ≤ etaMax j)
    (ρ : NontrivialZeros) (hcut : |(ρ : ℂ).im| ≤ T) :
    0 ≤ Pi j (2 * σ - 1) η (((σ : ℂ) + (τ : ℂ) * Complex.I) - ρ) := by
  have hl := zeros_below_cutoff hPT hA hmin (by rw [←hσdef]; exact hσhalf)
    ρ.property.2.2 ρ.property.1.1 ρ.property.1.2 hcut
  rw [←hσdef] at hl
  have hx : ((((σ : ℂ) + (τ : ℂ) * Complex.I) - (ρ : ℂ))).re ∈ Set.Icc (0 : ℝ) (2 * σ - 1) := by
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_I_re,
      Complex.ofReal_im, add_zero]
    constructor <;> linarith [hl.1, hl.2]
  exact paired_positivity j ⟨hh, by linarith⟩ hη hηmax hx

lemma lowPairedTerm_nonneg (hPT : PlattTrudgianInput) (j : Fin 7) {σ η τ A T : ℝ}
    (hA : 0 < A) (hmin : ∀ z : ℂ, Admissible z → A ≤ depth z)
    (hσdef : σ = 1 - A / Real.log T) (hσhalf : (1 / 2 : ℝ) < σ) (hσ1 : σ < 1)
    (hh : hMin j ≤ 2 * σ - 1) (hη : 0 < η) (hηmax : η ≤ etaMax j) (ρ : NontrivialZeros) :
    0 ≤ lowPairedTerm j σ η τ T ρ := by
  unfold lowPairedTerm
  split_ifs with hcut
  · have ho : 0 ≤ (riemannZeta.order ρ : ℝ) := by exact_mod_cast zeta_order_nonneg (nontrivial_ne_one ρ)
    exact mul_nonneg (Pi_low_zero_nonneg hPT j hA hmin hσdef hσhalf hσ1 hh hη hηmax ρ hcut) ho
  · exact le_rfl

lemma lowPairedTerm_summable (hK2 : KadiriExplicitInput) (j : Fin 7) {σ η τ T : ℝ}
    (hσhalf : (1 / 2 : ℝ) < σ) (hh : 0 ≤ 2 * σ - 1) (hη : 0 < η) :
    Summable (lowPairedTerm j σ η τ T) := by
  classical
  have hs := paired_zero_sum_summable hK2 j (s := (σ : ℂ) + (τ : ℂ) * Complex.I)
    hh hη (by simpa using hσhalf) (by simp)
  have hi := hs.indicator {ρ : NontrivialZeros | |(ρ : ℂ).im| ≤ T}
  apply hi.congr
  intro ρ
  simp only [lowPairedTerm, Set.indicator_apply, Set.mem_ofPred_eq]

@[blueprint "varlamov-distinguished-pair"
  (title := "Varlamov, Lemma 7.1: retaining the distinguished pair")
  (statement := /-- The low-zero paired sum retains twice the real pair term
  at the selected zero and its reflection. All other low terms are nonnegative.
  Positive multiplicities and distinctness are proved; the high-zero loss is
  a separate remaining estimate. -/)
  (uses := ["varlamov-zero-reflection-order", "varlamov-zero-localization",
    "varlamov-paired-positivity"])]
theorem distinguished_pair_low_sum (hK2 : KadiriExplicitInput) (hPT : PlattTrudgianInput)
    (j : Fin 7) {σ η τ A T : ℝ} (hA : 0 < A) (hmin : ∀ z : ℂ, Admissible z → A ≤ depth z)
    (hσdef : σ = 1 - A / Real.log T) (hσhalf : (1 / 2 : ℝ) < σ) (hσ1 : σ < 1)
    (hh : hMin j ≤ 2 * σ - 1) (hη : 0 < η) (hηmax : η ≤ etaMax j)
    (ρ₀ : NontrivialZeros) (hβ : (ρ₀ : ℂ).re = 1 - η) (hhalf : (1 / 2 : ℝ) < (ρ₀ : ℂ).re)
    (hτ : (ρ₀ : ℂ).im = τ) (hcut : |(ρ₀ : ℂ).im| ≤ T) :
    2 * mainPairValue j σ η ≤ ∑' ρ : NontrivialZeros, lowPairedTerm j σ η τ T ρ := by
  classical
  let ρ₁ := reflectZero ρ₀
  have hne : ρ₀ ≠ ρ₁ := by
    intro he
    have hre := congrArg (fun z : NontrivialZeros => (z : ℂ).re) he
    simp only [ρ₁, reflectZero, Complex.sub_re, Complex.one_re, Complex.conj_re] at hre
    linarith
  have hs := lowPairedTerm_summable hK2 j (τ := τ) (T := T) hσhalf ((hMin_pos j).le.trans hh) hη
  have hn (ρ : NontrivialZeros) := lowPairedTerm_nonneg hPT j (τ := τ) hA hmin hσdef hσhalf hσ1 hh hη hηmax ρ
  have hfirst : Pi j (2 * σ - 1) η (((σ : ℂ) + (τ : ℂ) * Complex.I) - (ρ₀ : ℂ)) = mainPairValue j σ η := by
    have hz : ((σ : ℂ) + (τ : ℂ) * Complex.I) - (ρ₀ : ℂ) = (((σ - 1 + η : ℝ)) : ℂ) := by
      apply Complex.ext <;> simp [hβ, hτ] <;> ring
    rw [hz, Pi]
    have hm : (((2 * σ - 1 : ℝ)) : ℂ) - conj (((σ - 1 + η : ℝ)) : ℂ) = (((σ - η : ℝ)) : ℂ) := by
      simp only [Complex.conj_ofReal]
      push_cast
      ring
    rw [hm]
    rfl
  have href : (((σ : ℂ) + (τ : ℂ) * Complex.I) - (ρ₁ : ℂ)) =
      (((2 * σ - 1 : ℝ)) : ℂ) - conj (((σ : ℂ) + (τ : ℂ) * Complex.I) - (ρ₀ : ℂ)) := by
    apply Complex.ext <;> simp [ρ₁, reflectZero] <;> ring
  have hsecond : Pi j (2 * σ - 1) η (((σ : ℂ) + (τ : ℂ) * Complex.I) - (ρ₁ : ℂ)) = mainPairValue j σ η := by
    rw [href, Pi_reflection, hfirst]
  have hV : 0 ≤ mainPairValue j σ η := by
    rw [←hfirst]
    exact Pi_low_zero_nonneg hPT j hA hmin hσdef hσhalf hσ1 hh hη hηmax ρ₀ hcut
  have ho0 : (1 : ℝ) ≤ riemannZeta.order ρ₀ := by exact_mod_cast nontrivial_order_pos ρ₀
  have ho1 : (1 : ℝ) ≤ riemannZeta.order ρ₁ := by exact_mod_cast nontrivial_order_pos ρ₁
  have hc1 : |(ρ₁ : ℂ).im| ≤ T := by simpa [ρ₁, reflectZero] using hcut
  have he0 : lowPairedTerm j σ η τ T ρ₀ = mainPairValue j σ η * (riemannZeta.order ρ₀ : ℝ) := by
    simp only [lowPairedTerm, ite_eq_left hcut, hfirst]
  have he1 : lowPairedTerm j σ η τ T ρ₁ = mainPairValue j σ η * (riemannZeta.order ρ₁ : ℝ) := by
    simp only [lowPairedTerm, ite_eq_left hc1, hsecond]
  have hkeep := Summable.sum_le_tsum ({ρ₀, ρ₁} : Finset NontrivialZeros) (fun ρ _ => hn ρ) hs
  rw [Finset.sum_pair hne, he0, he1] at hkeep
  have hm0 := mul_le_mul_of_nonneg_left ho0 hV
  have hm1 := mul_le_mul_of_nonneg_left ho1 hV
  nlinarith

#print axioms nontrivial_order_pos
#print axioms distinguished_pair_low_sum
end Varlamov
