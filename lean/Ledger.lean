import PrimeNumberTheoremAnd.IEANTN.Varlamov.PrimeFrequency
import PrimeNumberTheoremAnd.IEANTN.Varlamov.ZeroPairSplit
import PrimeNumberTheoremAnd.IEANTN.Varlamov.ExplicitFormula
import PrimeNumberTheoremAnd.IEANTN.Varlamov.GammaPositive
import PrimeNumberTheoremAnd.IEANTN.Varlamov.TailConstants

namespace Varlamov
open Real
open scoped BigOperators

noncomputable def frequencyPoint (σ t : ℝ) (k : ℕ) : ℂ :=
  (σ : ℂ) + (k : ℂ) * (t : ℂ) * Complex.I
noncomputable def weightedZeroSum (j : Fin 7) (σ h η t : ℝ) : ℝ :=
  ∑ k ∈ Finset.range 13, Trigonometric.a k *
    riemannZeta.zeroes_sum (Set.Ioo 0 1) Set.univ
      (fun ρ => (F j h η (frequencyPoint σ t k - ρ)).re)
noncomputable def pairD (j : Fin 7) (σ h η : ℝ) : ℝ :=
  Trigonometric.a 1 * ((F j h η (((σ - 1 + η : ℝ)) : ℂ)).re +
    (F j h η (((σ - η : ℝ)) : ℂ)).re) - (F j h η (((σ - 1 : ℝ)) : ℂ)).re

/-- The still unproved quantitative zero-sum obligation (the weighted
consequence of Lemma 7.1). It is NOT a published external input. -/
def WeightedZeroBound (j : Fin 7) (σ h η t : ℝ) : Prop :=
  Trigonometric.a 1 * ((F j h η (((σ - 1 + η : ℝ)) : ℂ)).re +
    (F j h η (((σ - η : ℝ)) : ℂ)).re) - zeroTailBudget j ≤ weightedZeroSum j σ h η t

lemma frequencyPoint_shift (σ h t : ℝ) (k m : ℕ) :
    frequencyPoint σ t k + ((h * (m : ℝ) : ℝ) : ℂ) =
      (((σ + h * (m : ℝ) : ℝ) : ℂ) + (k : ℂ) * (t : ℂ) * Complex.I) := by
  unfold frequencyPoint
  push_cast
  ring

lemma real_product_le_norm (c : ℝ) (z : ℂ) : c * z.re ≤ |c| * ‖z‖ := by
  calc
    _ ≤ |c * z.re| := le_abs_self _
    _ = |c| * |z.re| := abs_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm z) (abs_nonneg c)

lemma signed_remainder_bound (hC : HalfPlaneCauchyInput) (j : Fin 7) {σ h η t : ℝ}
    (hσ : sigmaMin j ≤ σ) (hh : hMin j ≤ h) (hη : 0 < η)
    (hηmax : η ≤ etaMax j) (ht : H ≤ |t|) :
    (∑ k ∈ Finset.range 13, Trigonometric.a k *
      (∑ m ∈ Finset.range (Multiplier.length j), Multiplier.coefficient j m *
        (Kernel.Delta η ((((σ + h * (m : ℝ) : ℝ) : ℂ) + (k : ℂ) * (t : ℂ) * Complex.I))).re)) ≤
      remainderE j * η ^ 3 := by
  apply le_trans ?_ (remainder_bound hC j hσ hh hη hηmax ht)
  apply Finset.sum_le_sum
  intro k hk
  apply mul_le_mul_of_nonneg_left _ (Trigonometric.a_nonneg ⟨k, Finset.mem_range.mp hk⟩)
  apply Finset.sum_le_sum
  intro m _
  exact real_product_le_norm _ _

lemma all_poles_bound (j : Fin 7) {σ h η t : ℝ}
    (hη : 0 < η) (hηmax : η ≤ etaMax j) (hσ : 1 - η ≤ σ) (hσ1 : σ ≤ 1)
    (hh : 0 ≤ h) (hh1 : h ≤ 1) (ht : H ≤ |t|) :
    (∑ k ∈ Finset.range 13, Trigonometric.a k * (F j h η (frequencyPoint σ t k - 1)).re) ≤
      (F j h η (((σ - 1 : ℝ)) : ℂ)).re + 1e-10 * η := by
  have hpoint (k : ℕ) : frequencyPoint σ t k - 1 =
      (((σ - 1 : ℝ) : ℂ) + (k : ℂ) * (t : ℂ) * Complex.I) := by
    unfold frequencyPoint
    push_cast
    ring
  simp_rw [hpoint]
  rw [show (13 : ℕ) = 12 + 1 from rfl, Finset.sum_range_succ']
  simp only [Nat.cast_zero, zero_mul, add_zero, Trigonometric.a_zero, one_mul]
  have hp := nonreal_pole_bound j hη hηmax hσ hσ1 hh hh1 ht
  linarith

lemma weighted_explicit_formula (hK2 : KadiriExplicitInput) (j : Fin 7) {σ h η t : ℝ}
    (hσ : (1 / 2 : ℝ) < σ) (hh : 0 ≤ h) (hη : 0 < η) :
    (∑' n : ℕ, primeContribution j σ h η t n) =
      η * 10 * (∑ k ∈ Finset.range 13, Trigonometric.a k *
        (∑ m ∈ Finset.range (Multiplier.length j), Multiplier.coefficient j m *
          gammaTerm ((((σ + h * (m : ℝ) : ℝ) : ℂ) + (k : ℂ) * (t : ℂ) * Complex.I)))) +
      (∑ k ∈ Finset.range 13, Trigonometric.a k * (F j h η (frequencyPoint σ t k - 1)).re) -
      weightedZeroSum j σ h η t +
      (∑ k ∈ Finset.range 13, Trigonometric.a k *
        (∑ m ∈ Finset.range (Multiplier.length j), Multiplier.coefficient j m *
          (Kernel.Delta η ((((σ + h * (m : ℝ) : ℝ) : ℂ) + (k : ℂ) * (t : ℂ) * Complex.I))).re)) := by
  rw [← prime_frequency_sum j hη σ h t]
  have hf (k : ℕ) := explicit_formula hK2 j hh hη
    (s := frequencyPoint σ t k) (by simpa [frequencyPoint] using hσ)
  simp_rw [frequencyPoint_shift] at hf
  change (∑ k ∈ Finset.range 13, Trigonometric.a k * primeSum (testFunction j h η) (frequencyPoint σ t k)) = _
  simp_rw [hf, mul_add, mul_sub, mul_add]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  unfold weightedZeroSum
  congr 3
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

@[blueprint "varlamov-conditional-ledger"
  (title := "Varlamov, Proposition 8.1: conditional ledger assembly")
  (statement := /-- The actual explicit formula and all signed bounds give
  the contradiction ledger, assuming the explicitly named remaining zero-sum
  obligation. J is the sum of the true phase infima, so no numerical phase
  assumption is needed for this version. The zero-sum obligation is not
  established here and is not a published input. -/)
  (uses := ["varlamov-explicit-formula", "varlamov-prime-frequency-bridge",
    "varlamov-prime-lifting", "varlamov-remainder-bound", "varlamov-gamma-factor",
    "varlamov-nonreal-pole", "varlamov-tail-constants"])]
theorem ledger_of_weighted_zero_bound (hK2 : KadiriExplicitInput) (hK3 : KadiriDigammaInput)
    (hC : HalfPlaneCauchyInput) (j : Fin 7) {σ h η t A : ℝ}
    (hσ : sigmaMin j ≤ σ) (hσmax : σ ≤ sigmaMax j) (hσ1 : σ ≤ 1) (hσeta : 1 - η ≤ σ)
    (hh : hMin j ≤ h) (hh1 : h ≤ 1) (hhmax : h ≤ 2 * sigmaMax j - 1)
    (hη : 0 < η) (hηmax : η ≤ etaMax j) (ht : H ≤ |t|) (hA : η * Real.log |t| = A)
    (hZeros : WeightedZeroBound j σ h η t) :
    pairD j σ h η + (gammaG j + primeLowerBudget j (primePhaseInf j)) * 10 * η -
      remainderE j * η ^ 3 - zeroTailBudget j - 1e-10 * η - gammaQ j * A ≤ 0 := by
  have hh0 : 0 ≤ h := (hMin_pos j).le.trans hh
  have hσhalf : (1 / 2 : ℝ) < σ := by linarith [(sigmaMin_range j).1]
  have hP := prime_powers_inf_lower_bound j (t := t) hη hηmax hh hσmax
  have hEq := weighted_explicit_formula hK2 j (t := t) hσhalf hh0 hη
  rw [hEq] at hP
  have hG := gamma_factor_bound hK3 j hσ hσmax hσ1 hh hh1 hhmax hη ht hA
  have hPole := all_poles_bound j hη hηmax hσeta hσ1 hh0 hh1 ht
  have hRem := signed_remainder_bound hC j hσ hh hη hηmax ht
  unfold WeightedZeroBound at hZeros
  unfold pairD
  nlinarith

lemma pairD_substitution (j : Fin 7) (μ η : ℝ) :
    pairD j (1 - μ * η) (1 - 2 * μ * η) η = zeroPairTerm j μ η := rfl

/-- The same ledger for any certified phase lower bounds, including the
manuscript's proposed numerical J_p after their C12 proofs are supplied. -/
theorem ledger_of_zero_bound_and_phase_certificate
    (hK2 : KadiriExplicitInput) (hK3 : KadiriDigammaInput) (hC : HalfPlaneCauchyInput)
    (j : Fin 7) (Jp : ℕ → ℝ) (hJ : PrimePhaseCertificate j Jp) {σ h η t A : ℝ}
    (hσ : sigmaMin j ≤ σ) (hσmax : σ ≤ sigmaMax j) (hσ1 : σ ≤ 1) (hσeta : 1 - η ≤ σ)
    (hh : hMin j ≤ h) (hh1 : h ≤ 1) (hhmax : h ≤ 2 * sigmaMax j - 1)
    (hη : 0 < η) (hηmax : η ≤ etaMax j) (ht : H ≤ |t|) (hA : η * Real.log |t| = A)
    (hZeros : WeightedZeroBound j σ h η t) :
    pairD j σ h η + (gammaG j + primeLowerBudget j Jp) * 10 * η -
      remainderE j * η ^ 3 - zeroTailBudget j - 1e-10 * η - gammaQ j * A ≤ 0 := by
  have hi := ledger_of_weighted_zero_bound hK2 hK3 hC j hσ hσmax hσ1 hσeta hh hh1 hhmax hη hηmax ht hA hZeros
  have hj := prime_budget_le_inf j Jp hJ
  have hm := mul_le_mul_of_nonneg_right hj (show 0 ≤ 10 * η by positivity)
  nlinarith

#print axioms ledger_of_zero_bound_and_phase_certificate
#print axioms ledger_of_weighted_zero_bound
end Varlamov
