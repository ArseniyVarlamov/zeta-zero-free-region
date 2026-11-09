import PrimeNumberTheoremAnd.IEANTN.Varlamov.PhaseWeightBridge
import PrimeNumberTheoremAnd.IEANTN.Varlamov.PhaseCertificate2P17

namespace Varlamov.PhaseWeights2P17
open Real
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000

lemma prime_selected : 17 ∈ selectedPrimes (1 : Fin 7) := by norm_num [selectedPrimes]

lemma weight_lower_1 : (558568904351 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (1 : Fin 7) 17 1 := by
  rw [primeOmegaWeight_piece (1 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa2, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_2 : (34897256334 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (1 : Fin 7) 17 2 := by
  rw [primeOmegaWeight_piece (1 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa2, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_3 : (2067795438 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (1 : Fin 7) 17 3 := by
  rw [primeOmegaWeight_piece (1 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa2, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_4 : (121960808 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (1 : Fin 7) 17 4 := by
  rw [primeOmegaWeight_piece (1 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa2, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_5 : (7182069 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (1 : Fin 7) 17 5 := by
  rw [primeOmegaWeight_piece (1 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa2, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_6 : (422361 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (1 : Fin 7) 17 6 := by
  rw [primeOmegaWeight_piece (1 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa2, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_7 : (24804 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (1 : Fin 7) 17 7 := by
  rw [primeOmegaWeight_piece (1 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa2, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_8 : (1453 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (1 : Fin 7) 17 8 := by
  rw [primeOmegaWeight_piece (1 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa2, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_9 : (84 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (1 : Fin 7) 17 9 := by
  rw [primeOmegaWeight_piece (1 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa2, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_10 : (3 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (1 : Fin 7) 17 10 := by
  rw [primeOmegaWeight_piece (1 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa2, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

theorem phase_lower (x : ℝ) :
    (((PhaseCertificate2P17.target - 1 : ℤ) : ℝ) / PhaseSOS.targetScale) ≤ primePhase (1 : Fin 7) 17 x := by
  apply (PhaseCertificate2P17.rounded_lower_bound x).trans
  apply roundedPhase_le_primePhase (1 : Fin 7) 17 PhaseCertificate2P17.weights
    (by norm_num [PhaseCertificate2P17.weights, powerCount]) ?_ x
  intro r hr
  norm_num [PhaseCertificate2P17.weights] at hr
  interval_cases r
  · simpa [PhaseCertificate2P17.weights, PhaseSOS.weightScale] using weight_lower_1
  · simpa [PhaseCertificate2P17.weights, PhaseSOS.weightScale] using weight_lower_2
  · simpa [PhaseCertificate2P17.weights, PhaseSOS.weightScale] using weight_lower_3
  · simpa [PhaseCertificate2P17.weights, PhaseSOS.weightScale] using weight_lower_4
  · simpa [PhaseCertificate2P17.weights, PhaseSOS.weightScale] using weight_lower_5
  · simpa [PhaseCertificate2P17.weights, PhaseSOS.weightScale] using weight_lower_6
  · simpa [PhaseCertificate2P17.weights, PhaseSOS.weightScale] using weight_lower_7
  · simpa [PhaseCertificate2P17.weights, PhaseSOS.weightScale] using weight_lower_8
  · simpa [PhaseCertificate2P17.weights, PhaseSOS.weightScale] using weight_lower_9
  · simpa [PhaseCertificate2P17.weights, PhaseSOS.weightScale] using weight_lower_10

#print axioms phase_lower
end Varlamov.PhaseWeights2P17
