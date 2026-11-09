import PrimeNumberTheoremAnd.IEANTN.Varlamov.Localization

/-!
# Exact remaining target and the zero-free tails

The equivalence below is a reduction, not a proof of `CompactExclusion`.
No unproved local analytic claim is accepted as a literature input.
-/

namespace Varlamov
open Real

lemma candidate_of_zero_in_region (hPT : PlattTrudgianInput) {σ t : ℝ}
    (ht : 2 ≤ |t|) (hσ : 1 - 1 / (R * log |t|) ≤ σ)
    (hz : riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) = 0) :
    ∃ z : ℂ, Candidate z ∧ z.re = σ ∧ z.im = |t| := by
  let w : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I
  have hhalf : 1 / 2 < w.re := by
    simpa [w] using (region_boundary_gt_half ht).trans_le hσ
  obtain ⟨z, hzA, hre, him⟩ := right_half_to_admissible hPT hz hhalf
  have hre' : z.re = σ := by simpa [w] using hre
  have him' : z.im = |t| := by simpa [w] using him
  refine ⟨z, ⟨hzA, ?_⟩, hre', him'⟩
  have hl : 0 < log |t| := log_pos (by linarith)
  have hd := (region_iff_depth hl (ne_of_gt R_pos)).mp hσ
  simpa [depth, hre', him', Astar_eq_one_div_R] using hd

@[blueprint "varlamov-zero-free-tails"
  (title := "Varlamov target outside the compact height window")
  (statement := /-- Assuming PT and Yang, the proposed $R=4.81406$ region
  is zero-free whenever $|t|\ge2$ and either $\log|t|\le28.7296$
  or $82.32067\le\log|t|$. Both crossover inequalities are checked in Lean. -/)
  (uses := ["varlamov-zero-free-target", "RH-up-to"])]
theorem zero_free_outside_window (hPT : PlattTrudgianInput) (hY : YangInput)
    {σ t : ℝ} (ht : 2 ≤ |t|) (hσ : 1 - 1 / (R * log |t|) ≤ σ)
    (hwindow : log |t| ≤ Llo ∨ Lhi ≤ log |t|) :
    riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
  intro hz
  obtain ⟨z, hzC, _, him⟩ := candidate_of_zero_in_region hPT ht hσ hz
  have h := candidate_log_height_mem hPT hY hzC
  rw [him] at h
  rcases hwindow with hlow | hhigh <;> linarith

/-- The explicitly bounded set whose exclusion is still required for the full target. -/
def CompactExclusion : Prop :=
  ∀ z : ℂ, riemannZeta z = 0 → 1 / 2 < z.re → H < z.im →
    Llo < log z.im → log z.im < Lhi →
    1 / 6 < depth z → depth z ≤ Astar → False

@[blueprint "varlamov-target-reduction"
  (title := "Exact reduction of Theorem 1.1 to compact zero exclusion")
  (statement := /-- Under the three published inputs, the target zero-free region
  is equivalent to the exclusion of the explicitly bounded zeros in Lemma 3.1.
  This theorem does not assume or prove that exclusion. -/)
  (uses := ["varlamov-minimal-zero", "varlamov-zero-free-target"])]
theorem zeroFreeRegion_iff_compactExclusion (hK : KadiriInput)
    (hPT : PlattTrudgianInput) (hY : YangInput) : ZeroFreeRegion ↔ CompactExclusion := by
  constructor
  · intro h z hz hhalf hH _ _ _ hA
    have ht : (2 : ℝ) ≤ |z.im| := by
      have hγ : 0 < z.im := lt_trans (by norm_num [H]) hH
      rw [abs_of_pos hγ]
      norm_num [H] at hH
      linarith
    have hγ : 0 < z.im := lt_trans (by norm_num [H]) hH
    have hl : 0 < log z.im := log_pos (by norm_num [H] at hH; linarith)
    have hσ : 1 - 1 / (R * log |z.im|) ≤ z.re := by
      rw [abs_of_pos hγ]
      apply (region_iff_depth hl (ne_of_gt R_pos)).mpr
      simpa [depth, Astar_eq_one_div_R] using hA
    have hn := h z.re z.im ht hσ
    exact hn ((Complex.re_add_im z).symm ▸ hz)
  · intro hex
    by_contra hfail
    obtain ⟨z, hz, hH, hA, hL, _⟩ := exists_minimal_zero hK hPT hY hfail
    exact hex z hz.1 hz.2.1 hH hL.1 hL.2 hA.1 hA.2

#print axioms zero_free_outside_window
#print axioms zeroFreeRegion_iff_compactExclusion

end Varlamov
