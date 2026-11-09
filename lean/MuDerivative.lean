import PrimeNumberTheoremAnd.IEANTN.Varlamov.Bands
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace Varlamov
open Real

lemma hasDerivAt_logCutoff (L : ℝ) :
    HasDerivAt logCutoff (12 * Real.exp L / (12 * Real.exp L + 10000000000)) L := by
  have hp : 0 < 12 * Real.exp L + 10000000000 := by positivity
  have hf := (((Real.hasDerivAt_exp L).const_mul 12).add_const 10000000000).log (ne_of_gt hp)
  convert hf using 1 <;> rfl

lemma exp_band_lower {L : ℝ} (hL : Llo ≤ L) : (2.9e12 : ℝ) < Real.exp L := by
  have h : (2.9e12 : ℝ) < Real.exp Llo := by
    norm_num [Llo]
    interval_decide (trust := kernel)
  exact h.trans_le (Real.exp_le_exp.mpr hL)

lemma logCutoff_sub_bounds {L : ℝ} (hL : Llo ≤ L) :
    0 < logCutoff L - L ∧ logCutoff L - L < (2.6 : ℝ) := by
  refine ⟨by linarith [logCutoff_gt (L := L)], ?_⟩
  have he := exp_band_lower hL
  have harg : 12 * Real.exp L + 10000000000 ≤ 13 * Real.exp L := by linarith
  have hlog := Real.log_le_log (by positivity : 0 < 12 * Real.exp L + 10000000000) harg
  have h13 : Real.log (13 : ℝ) < 2.6 := by interval_decide (trust := kernel)
  rw [Real.log_mul (by norm_num : (13 : ℝ) ≠ 0) (ne_of_gt (Real.exp_pos L)),
    Real.log_exp] at hlog
  change Real.log (12 * Real.exp L + 10000000000) - L < 2.6
  linarith

noncomputable def muSlope (L : ℝ) : ℝ :=
  (logCutoff L - L + L * (10000000000 / (12 * Real.exp L + 10000000000))) /
    (logCutoff L) ^ 2

lemma mu_hasDerivAt {L : ℝ} (hL : 0 < L) : HasDerivAt mu (muSlope L) L := by
  have hd : 0 < logCutoff L := hL.trans logCutoff_gt
  have hp : 0 < 12 * Real.exp L + 10000000000 := by positivity
  have he := (hasDerivAt_id L).div (hasDerivAt_logCutoff L) (ne_of_gt hd)
  simp only [id_eq, one_mul] at he
  convert he using 1
  · rfl
  · unfold muSlope
    field_simp
    <;> ring

lemma muSlope_bounds {L : ℝ} (hlo : Llo ≤ L) (hhi : L ≤ 83) :
    0 ≤ muSlope L ∧ muSlope L ≤ 3 / L ^ 2 := by
  have hL : 0 < L := (by norm_num [Llo] : (0 : ℝ) < Llo).trans_le hlo
  have hc := logCutoff_sub_bounds hlo
  have hd : 0 < logCutoff L := hL.trans logCutoff_gt
  have he := exp_band_lower hlo
  have hp : 0 < 12 * Real.exp L + 10000000000 := by positivity
  have hr0 : 0 ≤ (10000000000 : ℝ) / (12 * Real.exp L + 10000000000) := by positivity
  have hr : (10000000000 : ℝ) / (12 * Real.exp L + 10000000000) ≤ 1 / 3000 := by
    apply (div_le_iff₀ hp).mpr
    linarith
  have hn : 0 ≤ logCutoff L - L + L * (10000000000 / (12 * Real.exp L + 10000000000)) :=
    add_nonneg hc.1.le (mul_nonneg hL.le hr0)
  have hn3 : logCutoff L - L + L * (10000000000 / (12 * Real.exp L + 10000000000)) ≤ 3 := by
    have hprod := mul_le_mul hhi hr hr0 (by norm_num : (0 : ℝ) ≤ 83)
    linarith only [hc.2, hprod]
  constructor
  · exact div_nonneg hn (sq_nonneg _)
  · unfold muSlope
    calc
      _ ≤ 3 / (logCutoff L) ^ 2 := div_le_div_of_nonneg_right hn3 (sq_nonneg _)
      _ ≤ 3 / L ^ 2 := div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hL)
        (by nlinarith only [logCutoff_gt (L := L), hL])

#print axioms muSlope_bounds
lemma mu_domain_pos {L : ℝ} (hL : L ∈ Set.Icc Llo 83) : 0 < L :=
  (by norm_num [Llo] : (0 : ℝ) < Llo).trans_le hL.1

lemma mu_monotone : MonotoneOn mu (Set.Icc Llo 83) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc Llo 83)
  · intro L hL
    exact (mu_hasDerivAt (mu_domain_pos hL)).continuousAt.continuousWithinAt
  · intro L hL
    exact (mu_hasDerivAt (mu_domain_pos (interior_subset hL))).differentiableAt.differentiableWithinAt
  · intro L hL
    have hb : L ∈ Set.Icc Llo 83 := interior_subset hL
    rw [(mu_hasDerivAt (mu_domain_pos hb)).deriv]
    exact (muSlope_bounds hb.1 hb.2).1

noncomputable def muCompensation (L : ℝ) : ℝ := (1 / 2) * mu L + 8 * Astar * L⁻¹

lemma muCompensation_hasDerivAt {L : ℝ} (hL : 0 < L) :
    HasDerivAt muCompensation ((1 / 2) * muSlope L + 8 * Astar * (-1 / L ^ 2)) L := by
  have hi := ((hasDerivAt_id L).inv (ne_of_gt hL)).const_mul (8 * Astar)
  have he := ((mu_hasDerivAt hL).const_mul (1 / 2)).add hi
  convert he using 1 <;> (try dsimp only [muCompensation, id_eq]) <;> rfl

lemma muCompensation_antitone : AntitoneOn muCompensation (Set.Icc Llo 83) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc Llo 83)
  · intro L hL
    exact (muCompensation_hasDerivAt (mu_domain_pos hL)).continuousAt.continuousWithinAt
  · intro L hL
    exact (muCompensation_hasDerivAt (mu_domain_pos (interior_subset hL))).differentiableAt.differentiableWithinAt
  · intro L hL
    have hb : L ∈ Set.Icc Llo 83 := interior_subset hL
    rw [(muCompensation_hasDerivAt (mu_domain_pos hb)).deriv]
    have hs := mul_le_mul_of_nonneg_left (muSlope_bounds hb.1 hb.2).2
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
    calc
      _ ≤ (1 / 2) * (3 / L ^ 2) + 8 * Astar * (-1 / L ^ 2) := add_le_add hs le_rfl
      _ = ((3 / 2 : ℝ) - 8 * Astar) / L ^ 2 := by ring
      _ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by norm_num [Astar]) (sq_nonneg _)

#print axioms muCompensation_antitone
end Varlamov
