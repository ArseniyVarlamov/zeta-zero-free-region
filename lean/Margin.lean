import PrimeNumberTheoremAnd.IEANTN.Varlamov.Ledger
import PrimeNumberTheoremAnd.IEANTN.Varlamov.BandShift

namespace Varlamov
open Real
open scoped BigOperators

/-- The actual margin, with genuine W, G, E, Z, moments and phase data.
It is not the literal rational surrogate used in the numerical experiment. -/
noncomputable def margin (j : Fin 7) (Jp : ℕ → ℝ) (L A : ℝ) : ℝ :=
  taylorSum (mu L) - 1e-12 +
  Trigonometric.a 1 * (∑ m ∈ Finset.range (Multiplier.length j), Multiplier.coefficient j m *
    realW (argumentOne (mu L) (eta L A) m)) +
  (∑ n ∈ Finset.range (Multiplier.length j - 1), Multiplier.coefficient j (n + 1) *
    (Trigonometric.a 1 * realW (argumentTwo (mu L) (eta L A) (n + 1)) -
      realW (argumentThree (mu L) (eta L A) (n + 1)))) +
  (gammaG j + primeLowerBudget j Jp) * 10 * eta L A -
  remainderE j * (eta L A) ^ 3 - zeroTailBudget j - 1e-10 * eta L A - gammaQ j * A

/-- The C13 positivity predicate for the actual margin. Its concrete proof is in ActualMarginCertificate. -/
def MarginCertificate (Jp : Fin 7 → ℕ → ℝ) : Prop :=
  ∀ j : Fin 7, ∀ L A : ℝ, InBand j L A → (1e-6 : ℝ) < margin j (Jp j) L A

@[blueprint "varlamov-margin-reduction"
  (title := "Varlamov, final analytic reduction to the actual margin")
  (statement := /-- The actual margin is nonpositive at a point of a band
  with height at least H, provided the explicitly named remaining zero-sum
  bound and phase certificates hold. All analytic substitution, signed ledger,
  Dsplit and small-argument estimates are proved. Neither the zero-sum bound
  nor the positive numerical C13 margin is asserted here. -/)
  (uses := ["varlamov-conditional-ledger", "varlamov-zero-pair-split",
    "varlamov-small-arguments", "varlamov-band-bounds"])]
theorem margin_le_zero_of_zero_bound (hK2 : KadiriExplicitInput) (hK3 : KadiriDigammaInput)
    (hC : HalfPlaneCauchyInput) (j : Fin 7) (Jp : ℕ → ℝ) (hJ : PrimePhaseCertificate j Jp)
    {L A : ℝ} (hb : InBand j L A) (ht : H ≤ Real.exp L)
    (hZeros : WeightedZeroBound j (sigma L A) (2 * sigma L A - 1) (eta L A) (Real.exp L)) :
    margin j Jp L A ≤ 0 := by
  obtain ⟨hhalf, hσlo, hσhi, hmax, hη, hηmax, _, hμlo, hμhi⟩ := band_bounds j hb
  obtain ⟨hhlo, hhhi, hhmax⟩ := band_shift_bounds j hb
  have hL : 0 < L := (bandLo_pos j).trans_le hb.1.1
  have hlog : 0 < logCutoff L := hL.trans logCutoff_gt
  have hL0 : L ≠ 0 := ne_of_gt hL
  have hlog0 : logCutoff L ≠ 0 := ne_of_gt hlog
  have hσeq : sigma L A = 1 - mu L * eta L A := by
    unfold sigma mu eta
    field_simp
    <;> ring
  have hheq : 2 * sigma L A - 1 = 1 - 2 * mu L * eta L A := by rw [hσeq]; ring
  have hσeta : 1 - eta L A ≤ sigma L A := by rw [hσeq]; nlinarith
  have hσ1 : sigma L A ≤ 1 := hσhi.trans hmax.le
  have hh1 : 2 * sigma L A - 1 ≤ 1 := by linarith
  have ht' : H ≤ |Real.exp L| := by simpa only [abs_of_pos (Real.exp_pos L)] using ht
  have hA : eta L A * Real.log |Real.exp L| = A := by
    rw [abs_of_pos (Real.exp_pos L), Real.log_exp]
    unfold eta
    field_simp
  have hl := ledger_of_zero_bound_and_phase_certificate hK2 hK3 hC j Jp hJ
    hσlo.le hσhi hσ1 hσeta hhlo.le hh1 hhhi hη hηmax.le ht' hA hZeros
  have hD : pairD j (sigma L A) (2 * sigma L A - 1) (eta L A) = zeroPairTerm j (mu L) (eta L A) := by
    rw [hheq, hσeq]
    exact pairD_substitution j (mu L) (eta L A)
  rw [hD, zero_pair_split j (mu L) (ne_of_gt hη)] at hl
  have hs := small_arguments hμlo hμhi
  unfold margin
  nlinarith

#print axioms margin_le_zero_of_zero_bound
end Varlamov
