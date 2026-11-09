import PrimeNumberTheoremAnd.IEANTN.Varlamov.PairChecks

namespace Varlamov

/-- The exact h^- and h^+ bounds of Lemma 3.2, including the h^+ used by G. -/
theorem band_shift_bounds (j : Fin 7) {L A : ℝ} (hb : InBand j L A) :
    hMin j < 2 * sigma L A - 1 ∧ 2 * sigma L A - 1 ≤ 2 * sigmaMax j - 1 ∧ 2 * sigmaMax j - 1 < 1 := by
  obtain ⟨_, hσlo, hσhi, hmax, _⟩ := band_bounds j hb
  unfold hMin
  constructor
  · linarith
  · constructor <;> linarith

#print axioms band_shift_bounds
end Varlamov
