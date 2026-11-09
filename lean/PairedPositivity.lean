import PrimeNumberTheoremAnd.IEANTN.Varlamov.PairedBoundary
import PrimeNumberTheoremAnd.IEANTN.Varlamov.PairedVanishing

namespace Varlamov

lemma Pi_zero_edge (j : Fin 7) {h η : ℝ} (hh : hMin j ≤ h)
    (hη : 0 < η) (hηmax : η ≤ etaMax j) {z : ℂ} (hz : z.re = 0) :
    0 ≤ Pi j h η z := by
  have he : z = (z.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [hz]
  rw [he]
  exact Pi_boundary_nonneg j hh hη hηmax z.im

lemma Pi_vertical_edges (j : Fin 7) {h η : ℝ} (hh : hMin j ≤ h)
    (hη : 0 < η) (hηmax : η ≤ etaMax j) {z : ℂ} (hz : z.re = 0 ∨ z.re = h) :
    0 ≤ Pi j h η z := by
  rcases hz with hz | hz
  · exact Pi_zero_edge j hh hη hηmax hz
  · rw [← Pi_reflection j h η z]
    apply Pi_zero_edge j hh hη hηmax
    simp [hz]

/-- Vanishing at horizontal infinity makes the upper bound h<1 unnecessary
for the positivity argument; the paper's exact range is recorded below. -/
theorem paired_positivity_without_upper (j : Fin 7) {h η : ℝ}
    (hh : hMin j ≤ h) (hη : 0 < η) (hηmax : η ≤ etaMax j)
    {z : ℂ} (hz : z.re ∈ Set.Icc (0 : ℝ) h) : 0 ≤ Pi j h η z := by
  rw [Pi_analytic]
  apply paired_nonneg_of_boundary_and_vanishing (F_differentiable j h η) h ?_
    (F_vanishes_on_strip j ((hMin_pos j).trans_le hh).le hη) hz
  intro w hw
  rw [← Pi_analytic]
  exact Pi_vertical_edges j hh hη hηmax hw

@[blueprint "varlamov-paired-positivity"
  (title := "Varlamov, Proposition 5.2: paired positivity")
  (statement := /-- In each of the seven bands, for $h\in[h^-,1)$ and
  $0<\eta\le\eta^+$, the paired transform satisfies $\Pi(z)\ge0$
  throughout the closed strip $0\le\Re z\le h$.
  All numerical hypotheses C6 are proved here, with no literature input. -/)
  (uses := ["varlamov-paired-boundary-positive", "varlamov-transform-fourier-positive",
    "varlamov-transform-right-bound", "varlamov-transform-left-bound"])]
theorem paired_positivity (j : Fin 7) {h η : ℝ}
    (hh : h ∈ Set.Ico (hMin j) 1) (hη : 0 < η) (hηmax : η ≤ etaMax j)
    {z : ℂ} (hz : z.re ∈ Set.Icc (0 : ℝ) h) : 0 ≤ Pi j h η z :=
  paired_positivity_without_upper j hh.1 hη hηmax hz

#print axioms paired_positivity

end Varlamov
