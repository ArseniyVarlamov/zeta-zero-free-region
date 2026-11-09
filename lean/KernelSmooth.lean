import PrimeNumberTheoremAnd.IEANTN.Varlamov.TransformIBP
import PrimeNumberTheoremAnd.IEANTN.Varlamov.KernelSupport
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Topology.Order.OrderClosed

namespace Varlamov.Kernel
open Real Topology
open scoped ContDiff

noncomputable def cut (f : ℝ → ℝ) (u : ℝ) : ℝ := if u ≤ d then f u else 0

lemma cut_of_le {f : ℝ → ℝ} {u : ℝ} (hu : u ≤ d) : cut f u = f u := by simp [cut, hu]
lemma cut_of_gt {f : ℝ → ℝ} {u : ℝ} (hu : d < u) : cut f u = 0 := by simp [cut, not_le_of_gt hu]
lemma cut_zero_of_ge {f : ℝ → ℝ} (hf : f d = 0) {u : ℝ} (hu : d ≤ u) : cut f u = 0 := by
  by_cases h : u ≤ d
  · have he : u = d := le_antisymm h hu
    simp [cut, he, hf]
  · simp [cut, h]

lemma cut_continuous {f : ℝ → ℝ} (hc : Continuous f) (hf : f d = 0) : Continuous (cut f) := by
  unfold cut
  exact hc.if_le continuous_const continuous_id continuous_const (fun u hu => by simpa [hu] using hf)

lemma cut_hasDerivAt {f f' : ℝ → ℝ} (hf : f d = 0) (hf' : f' d = 0)
    (hd : ∀ u : ℝ, HasDerivAt f (f' u) u) (u : ℝ) :
    HasDerivAt (cut f) (cut f' u) u := by
  rcases lt_trichotomy u d with h | he | h
  · rw [cut_of_le h.le]
    apply (hd u).congr_of_eventuallyEq
    filter_upwards [isOpen_Iio.mem_nhds h] with v hv
    exact cut_of_le hv.le
  · subst u
    rw [cut_of_le le_rfl, hf']
    have hl : HasDerivWithinAt (cut f) (0 : ℝ) (Set.Iic d) d := by
      apply ((hd d).congr_deriv hf').hasDerivWithinAt.congr
      · intro v hv
        exact cut_of_le hv
      · exact cut_of_le le_rfl
    have hr : HasDerivWithinAt (cut f) (0 : ℝ) (Set.Ici d) d := by
      apply (hasDerivAt_const d (0 : ℝ)).hasDerivWithinAt.congr
      · intro v hv
        exact cut_zero_of_ge hf hv
      · exact cut_zero_of_ge hf le_rfl
    have hh := hl.union hr
    rw [Set.Iic_union_Ici, hasDerivWithinAt_univ] at hh
    exact hh
  · rw [cut_of_gt h]
    apply (hasDerivAt_const u (0 : ℝ)).congr_of_eventuallyEq
    filter_upwards [isOpen_Ioi.mem_nhds h] with v hv
    exact cut_of_gt hv

/-- Extending the polynomial piece by zero across d preserves two derivatives. -/
theorem contDiff_cut_piece : ContDiff ℝ 2 (cut piece) := by
  have h1d := piece_first_end
  have h2d := piece_second_end
  rw [iteratedDeriv_piece] at h1d h2d
  have hder0 (u : ℝ) : HasDerivAt piece (scaledDerivative 1 u) u := by
    simpa only [scaledDerivative_zero] using scaledDerivative_hasDerivAt 0 u
  have hder1 (u : ℝ) : HasDerivAt (scaledDerivative 1) (scaledDerivative 2 u) u :=
    scaledDerivative_hasDerivAt 1 u
  have hc0 (u : ℝ) : HasDerivAt (cut piece) (cut (scaledDerivative 1) u) u :=
    cut_hasDerivAt piece_at_end h1d hder0 u
  have hc1 (u : ℝ) : HasDerivAt (cut (scaledDerivative 1)) (cut (scaledDerivative 2) u) u :=
    cut_hasDerivAt h1d h2d hder1 u
  have hd0 : deriv (cut piece) = cut (scaledDerivative 1) := funext (fun u => (hc0 u).deriv)
  have hd1 : deriv (cut (scaledDerivative 1)) = cut (scaledDerivative 2) := funext (fun u => (hc1 u).deriv)
  have hcont2 : Continuous (cut (scaledDerivative 2)) :=
    cut_continuous (show Differentiable ℝ (scaledDerivative 2) from
      fun u => (scaledDerivative_hasDerivAt 2 u).differentiableAt).continuous h2d
  have hs1 : ContDiff ℝ 1 (cut (scaledDerivative 1)) :=
    contDiff_one_iff_deriv.mpr ⟨fun u => (hc1 u).differentiableAt, hd1.symm ▸ hcont2⟩
  have hs2 : ContDiff ℝ (1 + 1 : ℕ∞ω) (cut piece) :=
    contDiff_succ_iff_deriv.mpr
      ⟨fun u => (hc0 u).differentiableAt, by simp, hd0.symm ▸ hs1⟩
  exact hs2

lemma w_eq_cut_nonneg {u : ℝ} (hu : 0 ≤ u) : w u = cut piece u := by
  unfold w cut
  rw [abs_of_nonneg hu]

@[blueprint "varlamov-kernel-c2"
  (title := "Varlamov, Lemma 4.1(3): C2 regularity")
  (statement := /-- The actual compactly supported autocorrelation kernel is of class
  $C^2$ on $[0,\infty)$; the endpoint derivatives match the zero extension. -/)
  (uses := ["varlamov-kernel-autocorrelation", "varlamov-fourth-derivative-bound"])]
theorem w_contDiffOn : ContDiffOn ℝ 2 w (Set.Ici (0 : ℝ)) := by
  apply contDiff_cut_piece.contDiffOn.congr
  intro u hu
  exact w_eq_cut_nonneg hu

#print axioms contDiff_cut_piece
#print axioms w_contDiffOn

end Varlamov.Kernel
