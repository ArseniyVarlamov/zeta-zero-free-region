import PrimeNumberTheoremAnd.IEANTN.Varlamov.PairedMinimum

namespace Varlamov
open Real

noncomputable def stripRectangle (h Y : ℝ) : Set ℂ :=
  (Complex.re ⁻¹' Set.Icc (0 : ℝ) h) ∩ (Complex.im ⁻¹' Set.Icc (-Y) Y)

lemma stripRectangle_compact (h Y : ℝ) : IsCompact (stripRectangle h Y) := by
  exact Complex.equivRealProdCLM.toHomeomorph.isClosedEmbedding.isCompact_preimage
    (isCompact_Icc.prod isCompact_Icc)

lemma stripRectangle_frontier {h Y : ℝ} {z : ℂ}
    (hz : z ∈ frontier (stripRectangle h Y)) :
    z ∈ stripRectangle h Y ∧
      (z.re = 0 ∨ z.re = h ∨ z.im = -Y ∨ z.im = Y) := by
  have hc := stripRectangle_compact h Y
  have hm : z ∈ stripRectangle h Y := by
    simpa only [hc.isClosed.closure_eq] using (frontier_subset_closure hz)
  refine ⟨hm, ?_⟩
  have hn := (mem_frontier_iff_notMem_interior hm).mp hz
  by_contra hne
  push Not at hne
  rcases hne with ⟨h0, hh, hminus, hplus⟩
  let O : Set ℂ := (Complex.re ⁻¹' Set.Ioo (0 : ℝ) h) ∩
    (Complex.im ⁻¹' Set.Ioo (-Y) Y)
  have hO : IsOpen O := (isOpen_Ioo.preimage Complex.continuous_re).inter
    (isOpen_Ioo.preimage Complex.continuous_im)
  have hzO : z ∈ O := by
    exact ⟨⟨lt_of_not_ge (fun hh' => h0 (le_antisymm hh' hm.1.1)),
      lt_of_not_ge (fun hh' => hh (le_antisymm hm.1.2 hh'))⟩,
      ⟨lt_of_not_ge (fun hh' => hminus (le_antisymm hh' hm.2.1)),
      lt_of_not_ge (fun hh' => hplus (le_antisymm hm.2.2 hh'))⟩⟩
  have hsub : O ⊆ stripRectangle h Y := by
    intro w hw
    exact ⟨⟨hw.1.1.le, hw.1.2.le⟩, ⟨hw.2.1.le, hw.2.2.le⟩⟩
  exact hn ((interior_mono hsub) (hO.interior_eq.symm ▸ hzO))

/-- The analytic strip step of Proposition 5.2. Boundary and far-height
estimates remain explicit lemma hypotheses, not claimed literature inputs. -/
theorem paired_nonneg_of_boundary_and_far {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (h : ℝ)
    (hvertical : ∀ z : ℂ, z.re = 0 ∨ z.re = h →
      0 ≤ (F z + F ((h : ℂ) - z)).re)
    (hfar : ∃ Y₀ : ℝ, ∀ z : ℂ, z.re ∈ Set.Icc (0 : ℝ) h → Y₀ ≤ |z.im| →
      0 ≤ (F z + F ((h : ℂ) - z)).re)
    {z : ℂ} (hz : z.re ∈ Set.Icc (0 : ℝ) h) :
    0 ≤ (F z + F ((h : ℂ) - z)).re := by
  obtain ⟨Y₀, hfar⟩ := hfar
  let Y : ℝ := |z.im| + |Y₀| + 1
  have hY : 0 < Y := by dsimp [Y]; positivity
  have hY₀ : Y₀ ≤ Y := by dsimp [Y]; linarith [le_abs_self Y₀, abs_nonneg z.im]
  have hzS : z ∈ stripRectangle h Y := by
    refine ⟨hz, ?_⟩
    constructor <;> dsimp [Y] <;>
      linarith [le_abs_self z.im, neg_abs_le z.im, abs_nonneg Y₀]
  have hG : Differentiable ℂ (fun w => F w + F ((h : ℂ) - w)) := by fun_prop
  apply re_nonneg_of_frontier (stripRectangle_compact h Y).isBounded
    hG.diffContOnCl ?_ (subset_closure hzS)
  intro w hw
  obtain ⟨hwS, hwcase⟩ := stripRectangle_frontier hw
  rcases hwcase with hw0 | hwh | hwminus | hwplus
  · exact hvertical w (Or.inl hw0)
  · exact hvertical w (Or.inr hwh)
  · exact hfar w hwS.1 (by simpa [hwminus, abs_of_pos hY] using hY₀)
  · exact hfar w hwS.1 (by simpa [hwplus, abs_of_pos hY] using hY₀)

#print axioms paired_nonneg_of_boundary_and_far

end Varlamov
