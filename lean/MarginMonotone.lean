import PrimeNumberTheoremAnd.IEANTN.Varlamov.MarginDomain
import PrimeNumberTheoremAnd.IEANTN.Varlamov.MarginExpressionSemantics
import PrimeNumberTheoremAnd.IEANTN.Varlamov.MuDerivative

namespace Varlamov.MarginExpression
open Real

lemma band_parameter_bounds (j : Fin 7) {L A : ℝ} (hb : InBand j L A) :
    mu L ∈ Set.Icc (9 / 10 : ℝ) 1 ∧ eta L A ∈ Set.Icc (1 / (6 * bandHi j)) (etaMax j) := by
  obtain ⟨_,_,_,_,_,hη,_,hμ0,hμ1⟩ := band_bounds j hb
  have hL : 0 < L := (bandLo_pos j).trans_le hb.1.1
  refine ⟨⟨hμ0.le,hμ1.le⟩,⟨?_,hη.le⟩⟩
  change 1 / (6 * bandHi j) ≤ A / L
  calc
    _ = (1 / 6 : ℝ) / bandHi j := by ring
    _ ≤ (1 / 6 : ℝ) / L := div_le_div_of_nonneg_left (by norm_num) hL hb.1.2
    _ ≤ A / L := div_le_div_of_nonneg_right hb.2.1 hL.le

lemma eta_sub_bounds (j : Fin 7) (hc : checkRange j (fullBox j) 1 8 50 = true)
    {μ A a b : ℝ} (hμ : μ ∈ Set.Icc (9 / 10 : ℝ) 1)
    (hA : A ∈ Set.Icc (1 / 6 : ℝ) Astar)
    (ha : a ∈ Set.Icc (1 / (6 * bandHi j)) (etaMax j))
    (hb : b ∈ Set.Icc (1 / (6 * bandHi j)) (etaMax j)) (hab : a ≤ b) :
    8 * (b - a) ≤ value j μ b A - value j μ a A ∧
      value j μ b A - value j μ a A ≤ 50 * (b - a) := by
  apply sub_bounds_of_deriv hab (by norm_num : (0 : ℝ) < 8)
  intro x hx
  exact eta_derivative_bounds j hc hμ ha hA ⟨ha.1.trans hx.1,hx.2.trans hb.2⟩

lemma mu_sub_bounds (j : Fin 7) (hc : checkRange j (fullBox j) 0 (1/10) (1/2) = true)
    {η A a b : ℝ} (hη : η ∈ Set.Icc (1 / (6 * bandHi j)) (etaMax j))
    (hA : A ∈ Set.Icc (1 / 6 : ℝ) Astar)
    (ha : a ∈ Set.Icc (9 / 10 : ℝ) 1) (hb : b ∈ Set.Icc (9 / 10 : ℝ) 1) (hab : a ≤ b) :
    (1/10 : ℝ) * (b - a) ≤ value j b η A - value j a η A ∧
      value j b η A - value j a η A ≤ (1/2 : ℝ) * (b - a) := by
  apply sub_bounds_of_deriv hab (by norm_num : (0 : ℝ) < 1/10)
  intro x hx
  exact mu_derivative_bounds j hc ha hη hA ⟨ha.1.trans hx.1,hx.2.trans hb.2⟩

lemma Astar_mem : Astar ∈ Set.Icc (1 / 6 : ℝ) Astar := by norm_num [Astar]
lemma Astar_pos : (0 : ℝ) < Astar := by norm_num [Astar]
lemma bandHi_le_83 (j : Fin 7) : bandHi j ≤ (83 : ℝ) := by fin_cases j <;> norm_num [bandHi]
lemma data_q_lower (j : Fin 7) : (8 : ℝ) ≤ (data j).q := by fin_cases j <;> norm_num [data]

lemma value_Astar_le (j : Fin 7) (hc : checkRange j (fullBox j) 1 8 50 = true)
    {L A : ℝ} (hb : InBand j L A) :
    value j (mu L) (eta L Astar) Astar ≤ value j (mu L) (eta L A) A := by
  have hstar : InBand j L Astar := ⟨hb.1,Astar_mem⟩
  obtain ⟨hμ,hη⟩ := band_parameter_bounds j hb
  have hηstar := (band_parameter_bounds j hstar).2
  have hL : 0 < L := (bandLo_pos j).trans_le hb.1.1
  have hηle : eta L A ≤ eta L Astar := div_le_div_of_nonneg_right hb.2.2 hL.le
  have hv := (eta_sub_bounds j hc hμ Astar_mem hη hηstar hηle).2
  have hLlo : Llo ≤ L := (bandLo_ge j).trans hb.1.1
  have h50 : (50 : ℝ) / L ≤ 8 := (div_le_iff₀ hL).mpr (by norm_num [Llo] at hLlo; linarith)
  have hq : (50 : ℝ) / L ≤ (data j).q := h50.trans (data_q_lower j)
  have hm := mul_le_mul_of_nonneg_right hq (sub_nonneg.mpr hb.2.2)
  have hm' : 50 * (eta L Astar - eta L A) ≤ ((data j).q : ℝ) * (Astar - A) := by
    convert hm using 1 <;> unfold eta <;> ring
  rw [value_affine_A j (mu L) (eta L A) A Astar]
  linarith only [hv,hm']

lemma value_corner_le_Astar (j : Fin 7)
    (hcμ : checkRange j (fullBox j) 0 (1/10) (1/2) = true)
    (hcη : checkRange j (fullBox j) 1 8 50 = true)
    {L A : ℝ} (hb : InBand j L A) :
    value j (mu (bandHi j)) (eta (bandHi j) Astar) Astar ≤ value j (mu L) (eta L Astar) Astar := by
  have hstar : InBand j L Astar := ⟨hb.1,Astar_mem⟩
  have hcorner : InBand j (bandHi j) Astar := ⟨⟨(band_endpoints j).le,le_rfl⟩,Astar_mem⟩
  obtain ⟨hμ,hη⟩ := band_parameter_bounds j hstar
  obtain ⟨hμhi,hηhi⟩ := band_parameter_bounds j hcorner
  have hLlo : Llo ≤ L := (bandLo_ge j).trans hb.1.1
  have hHilo : Llo ≤ bandHi j := (bandLo_ge j).trans (band_endpoints j).le
  have hLdom : L ∈ Set.Icc Llo 83 := ⟨hLlo,hb.1.2.trans (bandHi_le_83 j)⟩
  have hHidom : bandHi j ∈ Set.Icc Llo 83 := ⟨hHilo,bandHi_le_83 j⟩
  have hL : 0 < L := mu_domain_pos hLdom
  have hμle := mu_monotone hLdom hHidom hb.1.2
  have hηle : eta (bandHi j) Astar ≤ eta L Astar :=
    div_le_div_of_nonneg_left Astar_pos.le hL hb.1.2
  have h1 := (eta_sub_bounds j hcη hμ Astar_mem hηhi hη hηle).1
  have h2 := (mu_sub_bounds j hcμ hηhi Astar_mem hμ hμhi hμle).2
  have h3 := muCompensation_antitone hLdom hHidom hb.1.2
  have h3' : (1/2 : ℝ) * mu (bandHi j) + 8 * eta (bandHi j) Astar ≤
      (1/2 : ℝ) * mu L + 8 * eta L Astar := by
    simpa only [muCompensation, eta, div_eq_mul_inv, mul_assoc] using h3
  linarith only [h1,h2,h3']

/-- The compensated mean-value argument covers the entire closed parameter
rectangle, so no unverified finite grid coverage is used. -/
theorem value_corner_le (j : Fin 7)
    (hcμ : checkRange j (fullBox j) 0 (1/10) (1/2) = true)
    (hcη : checkRange j (fullBox j) 1 8 50 = true)
    {L A : ℝ} (hb : InBand j L A) :
    value j (mu (bandHi j)) (eta (bandHi j) Astar) Astar ≤ value j (mu L) (eta L A) A :=
  (value_corner_le_Astar j hcμ hcη hb).trans (value_Astar_le j hcη hb)

#print axioms value_corner_le
end Varlamov.MarginExpression
