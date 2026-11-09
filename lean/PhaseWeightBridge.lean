import PrimeNumberTheoremAnd.IEANTN.Varlamov.PhaseSOS

namespace Varlamov
open Real
open scoped BigOperators

lemma primeOmegaWeight_piece (j : Fin 7) {p r : ℕ} (hp : p ∈ selectedPrimes j)
    (hr : r ∈ Finset.Icc 1 (powerCount j)) :
    primeOmegaWeight j p r =
      Multiplier.kappa j (Real.exp (-hMin j * (r : ℝ) * Real.log p)) *
        (Kernel.piece (etaMax j * (r : ℝ) * Real.log p) / 10) *
          Real.exp (-sigmaMax j * (r : ℝ) * Real.log p) := by
  have ha := prime_kernel_argument j hp hr
  unfold primeOmegaWeight
  rw [Kernel.w_piece ⟨ha.1.le, ha.2.le.trans (by norm_num [Kernel.d])⟩]

lemma roundedPhase_le_primePhase (j : Fin 7) (p : ℕ) (weights : List ℤ)
    (hlen : weights.length = powerCount j)
    (hw : ∀ r < weights.length,
      ((weights.getD r 0 : ℤ) : ℝ) / PhaseSOS.weightScale ≤ primeOmegaWeight j p (r + 1))
    (x : ℝ) : PhaseSOS.roundedPhase weights x ≤ primePhase j p x := by
  unfold PhaseSOS.roundedPhase primePhase
  rw [← hlen]
  apply Finset.sum_le_sum
  intro r hr
  exact mul_le_mul_of_nonneg_right (hw r (Finset.mem_range.mp hr)) (Trigonometric.P_nonneg _)

end Varlamov
