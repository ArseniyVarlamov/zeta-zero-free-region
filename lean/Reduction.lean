import PrimeNumberTheoremAnd.IEANTN.Varlamov.Numbers

/-!
# Section 3: the minimal-zero reduction

Only the three published inputs (K1), (PT), and (Y) occur as assumptions.
Compact-zero finiteness and conjugation are proved by the imported libraries.
-/

namespace Varlamov
open Real
open scoped ComplexConjugate

lemma admissible_height_gt (hPT : PlattTrudgianInput) {z : ℂ}
    (hz : Admissible z) : H < z.im := by
  by_contra hh
  have hmem : z ∈ riemannZeta.zeroes_rect (Set.Ioo 0.5 1) (Set.Icc 0 H) := by
    exact ⟨⟨by linarith [hz.2.1], zeta_re_lt_one hz.1⟩,
      ⟨hz.2.2.le, le_of_not_gt hh⟩, hz.1⟩
  exact hPT.false ⟨z, hmem⟩

lemma admissible_depth_lower (hK : KadiriInput) (hPT : PlattTrudgianInput)
    {z : ℂ} (hz : Admissible z) : (1 / 6 : ℝ) < depth z := by
  have hH := admissible_height_gt hPT hz
  have ht : 2 ≤ z.im := by dsimp [H] at hH; linarith
  have hlog : 0 < log z.im := log_pos (by linarith)
  have hk : (1 / (5.69693 : ℝ)) < depth z := by
    by_contra h
    have hd : (1 - z.re) * log z.im ≤ 1 / (5.69693 : ℝ) := le_of_not_gt h
    have hσ := (region_iff_depth hlog (by norm_num : (5.69693 : ℝ) ≠ 0)).mpr hd
    have he : (z.re : ℂ) + (z.im : ℂ) * Complex.I = z := Complex.re_add_im z
    exact hK z.re z.im ht hσ (he.symm ▸ hz.1)
  exact lt_trans (by norm_num) hk

lemma admissible_yang_depth (hY : YangInput) (hPT : PlattTrudgianInput)
    {z : ℂ} (hz : Admissible z) : log (log z.im) / 21.233 ≤ depth z := by
  have hH := admissible_height_gt hPT hz
  have ht : 3 ≤ z.im := by dsimp [H] at hH; linarith
  have hlog : 0 < log z.im := log_pos (by linarith)
  by_contra hn
  have hd : (1 - z.re) * log z.im < log (log z.im) / 21.233 := lt_of_not_ge hn
  have hd' : 1 - z.re < (log (log z.im) / 21.233) / log z.im :=
    (lt_div_iff₀ hlog).mpr hd
  have hσ : 1 - log (log z.im) / (21.233 * log z.im) < z.re := by
    have he : (log (log z.im) / 21.233) / log z.im =
        log (log z.im) / (21.233 * log z.im) := by ring
    rw [he] at hd'
    linarith
  have he : (z.re : ℂ) + (z.im : ℂ) * Complex.I = z := Complex.re_add_im z
  exact hY z.re z.im ht hσ (he.symm ▸ hz.1)

lemma candidate_log_height_mem (hPT : PlattTrudgianInput) (hY : YangInput)
    {z : ℂ} (hz : Candidate z) : Llo < log z.im ∧ log z.im < Lhi := by
  have hH := admissible_height_gt hPT hz.1
  have hH0 : 0 < H := by norm_num [H]
  have hlog := lt_trans Llo_lt_log_H (log_lt_log hH0 hH)
  refine ⟨hlog, ?_⟩
  have hy := admissible_yang_depth hY hPT hz.1
  have hyy : log (log z.im) ≤ 21.233 * Astar := by
    have := (div_le_iff₀ (by norm_num : (0 : ℝ) < 21.233)).mp (hy.trans hz.2)
    nlinarith
  have hlt : log (log z.im) < log Lhi := hyy.trans_lt yang_endpoint
  exact (log_lt_log_iff (by dsimp [Llo] at hlog; linarith)
    (by norm_num [Lhi])).mp hlt

lemma candidate_set_finite (hPT : PlattTrudgianInput) (hY : YangInput) :
    {z : ℂ | Candidate z}.Finite := by
  let S : Set ℂ := (Complex.re ⁻¹' Set.Icc (0 : ℝ) 1) ∩
    (Complex.im ⁻¹' Set.Icc (0 : ℝ) (exp Lhi))
  have hS : IsCompact S := by
    exact Complex.equivRealProdCLM.toHomeomorph.isClosedEmbedding.isCompact_preimage
      (isCompact_Icc.prod isCompact_Icc)
  refine (riemannZeta.zeroes_on_Compact_finite' hS).subset ?_
  intro z hz
  have hlt := (candidate_log_height_mem hPT hY hz).2
  have him : z.im < exp Lhi := (log_lt_iff_lt_exp hz.1.2.2).mp hlt
  exact ⟨⟨⟨by linarith [hz.1.2.1], (zeta_re_lt_one hz.1.1).le⟩,
    ⟨hz.1.2.2.le, him.le⟩⟩, hz.1.1⟩

lemma candidate_of_counterexample (h : ¬ ZeroFreeRegion) :
    ∃ z : ℂ, Candidate z := by
  classical
  unfold ZeroFreeRegion at h
  push Not at h
  obtain ⟨σ, t, ht, hσ, hz⟩ := h
  have hpos : 0 < |t| := by linarith
  have hlog : 0 < log |t| := log_pos (by linarith)
  have hhalf : 1 / 2 < σ := (region_boundary_gt_half ht).trans_le hσ
  have hd : (1 - σ) * log |t| ≤ Astar := by
    rw [Astar_eq_one_div_R]
    exact (region_iff_depth hlog (ne_of_gt R_pos)).mp hσ
  let z : ℂ := (σ : ℂ) + ((|t| : ℝ) : ℂ) * Complex.I
  have hz' : riemannZeta z = 0 := by
    rcases le_or_gt 0 t with ht0 | ht0
    · simpa [z, abs_of_nonneg ht0] using hz
    · have hc := zeta_eq_zero_conj hz
      simpa [z, abs_of_neg ht0, map_add, map_mul] using hc
  refine ⟨z, ⟨hz', ?_, ?_⟩, ?_⟩
  · simpa [z] using hhalf
  · simpa [z] using hpos
  · simpa [z, depth] using hd

@[blueprint "varlamov-minimal-zero"
  (title := "Varlamov, Lemma 3.1: minimal zero")
  (statement := /-- If the proposed theorem fails, a positive-height zero to the right
  of the critical line minimizes $(1-\beta)\log\gamma$ over all such zeros. It has
  height above $3\cdot10^{12}$, $1/6<A\le 50000/240703$, and
  $28.7296<\log\gamma<82.32067$. The only external inputs are Kadiri,
  Platt--Trudgian, and Yang. -/)
  (uses := ["varlamov-zero-free-target", "RH-up-to"])]
theorem exists_minimal_zero (hK : KadiriInput) (hPT : PlattTrudgianInput)
    (hY : YangInput) (hfail : ¬ ZeroFreeRegion) :
    ∃ z : ℂ, Admissible z ∧ H < z.im ∧
      (1 / 6 < depth z ∧ depth z ≤ Astar) ∧
      (Llo < log z.im ∧ log z.im < Lhi) ∧
      ∀ w : ℂ, Admissible w → depth z ≤ depth w := by
  obtain ⟨w, hw⟩ := candidate_of_counterexample hfail
  obtain ⟨z, hz, hmin⟩ := Set.exists_min_image {z : ℂ | Candidate z}
    depth (candidate_set_finite hPT hY) ⟨w, hw⟩
  refine ⟨z, hz.1, admissible_height_gt hPT hz.1,
    ⟨admissible_depth_lower hK hPT hz.1, hz.2⟩,
    candidate_log_height_mem hPT hY hz, ?_⟩
  intro w hw
  by_cases hd : depth w ≤ Astar
  · exact hmin w ⟨hw, hd⟩
  · exact hz.2.trans (le_of_lt (lt_of_not_ge hd))

#print axioms exists_minimal_zero

end Varlamov
