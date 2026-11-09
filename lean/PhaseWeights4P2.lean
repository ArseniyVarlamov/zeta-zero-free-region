import PrimeNumberTheoremAnd.IEANTN.Varlamov.PhaseWeightBridge
import PrimeNumberTheoremAnd.IEANTN.Varlamov.PhaseCertificate4P2

namespace Varlamov.PhaseWeights4P2
open Real
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000

lemma prime_selected : 2 ∈ selectedPrimes (3 : Fin 7) := by norm_num [selectedPrimes]

lemma weight_lower_1 : (3333696026001 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (3 : Fin 7) 2 1 := by
  rw [primeOmegaWeight_piece (3 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa4, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_2 : (2002477017585 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (3 : Fin 7) 2 2 := by
  rw [primeOmegaWeight_piece (3 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa4, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_3 : (1114293323373 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (3 : Fin 7) 2 3 := by
  rw [primeOmegaWeight_piece (3 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa4, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_4 : (590930923605 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (3 : Fin 7) 2 4 := by
  rw [primeOmegaWeight_piece (3 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa4, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_5 : (304912456370 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (3 : Fin 7) 2 5 := by
  rw [primeOmegaWeight_piece (3 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa4, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_6 : (155031825477 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (3 : Fin 7) 2 6 := by
  rw [primeOmegaWeight_piece (3 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa4, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_7 : (78223468337 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (3 : Fin 7) 2 7 := by
  rw [primeOmegaWeight_piece (3 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa4, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_8 : (39313752168 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (3 : Fin 7) 2 8 := by
  rw [primeOmegaWeight_piece (3 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa4, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_9 : (19718718898 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (3 : Fin 7) 2 9 := by
  rw [primeOmegaWeight_piece (3 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa4, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_10 : (9880178873 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (3 : Fin 7) 2 10 := by
  rw [primeOmegaWeight_piece (3 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa4, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

theorem phase_lower (x : ℝ) :
    (((PhaseCertificate4P2.target - 1 : ℤ) : ℝ) / PhaseSOS.targetScale) ≤ primePhase (3 : Fin 7) 2 x := by
  apply (PhaseCertificate4P2.rounded_lower_bound x).trans
  apply roundedPhase_le_primePhase (3 : Fin 7) 2 PhaseCertificate4P2.weights
    (by norm_num [PhaseCertificate4P2.weights, powerCount]) ?_ x
  intro r hr
  norm_num [PhaseCertificate4P2.weights] at hr
  interval_cases r
  · simpa [PhaseCertificate4P2.weights, PhaseSOS.weightScale] using weight_lower_1
  · simpa [PhaseCertificate4P2.weights, PhaseSOS.weightScale] using weight_lower_2
  · simpa [PhaseCertificate4P2.weights, PhaseSOS.weightScale] using weight_lower_3
  · simpa [PhaseCertificate4P2.weights, PhaseSOS.weightScale] using weight_lower_4
  · simpa [PhaseCertificate4P2.weights, PhaseSOS.weightScale] using weight_lower_5
  · simpa [PhaseCertificate4P2.weights, PhaseSOS.weightScale] using weight_lower_6
  · simpa [PhaseCertificate4P2.weights, PhaseSOS.weightScale] using weight_lower_7
  · simpa [PhaseCertificate4P2.weights, PhaseSOS.weightScale] using weight_lower_8
  · simpa [PhaseCertificate4P2.weights, PhaseSOS.weightScale] using weight_lower_9
  · simpa [PhaseCertificate4P2.weights, PhaseSOS.weightScale] using weight_lower_10

#print axioms phase_lower
end Varlamov.PhaseWeights4P2
