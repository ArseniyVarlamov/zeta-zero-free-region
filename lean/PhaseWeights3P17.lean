import PrimeNumberTheoremAnd.IEANTN.Varlamov.PhaseWeightBridge
import PrimeNumberTheoremAnd.IEANTN.Varlamov.PhaseCertificate3P17

namespace Varlamov.PhaseWeights3P17
open Real
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000

lemma prime_selected : 17 ∈ selectedPrimes (2 : Fin 7) := by norm_num [selectedPrimes]

lemma weight_lower_1 : (558358804950 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (2 : Fin 7) 17 1 := by
  rw [primeOmegaWeight_piece (2 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa3, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_2 : (34871376062 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (2 : Fin 7) 17 2 := by
  rw [primeOmegaWeight_piece (2 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa3, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_3 : (2067318202 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (2 : Fin 7) 17 3 := by
  rw [primeOmegaWeight_piece (2 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa3, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_4 : (122072850 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (2 : Fin 7) 17 4 := by
  rw [primeOmegaWeight_piece (2 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa3, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_5 : (7201183 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (2 : Fin 7) 17 5 := by
  rw [primeOmegaWeight_piece (2 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa3, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_6 : (424467 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (2 : Fin 7) 17 6 := by
  rw [primeOmegaWeight_piece (2 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa3, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_7 : (24999 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (2 : Fin 7) 17 7 := by
  rw [primeOmegaWeight_piece (2 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa3, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_8 : (1470 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (2 : Fin 7) 17 8 := by
  rw [primeOmegaWeight_piece (2 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa3, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_9 : (85 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (2 : Fin 7) 17 9 := by
  rw [primeOmegaWeight_piece (2 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa3, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_10 : (4 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (2 : Fin 7) 17 10 := by
  rw [primeOmegaWeight_piece (2 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa3, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

theorem phase_lower (x : ℝ) :
    (((PhaseCertificate3P17.target - 1 : ℤ) : ℝ) / PhaseSOS.targetScale) ≤ primePhase (2 : Fin 7) 17 x := by
  apply (PhaseCertificate3P17.rounded_lower_bound x).trans
  apply roundedPhase_le_primePhase (2 : Fin 7) 17 PhaseCertificate3P17.weights
    (by norm_num [PhaseCertificate3P17.weights, powerCount]) ?_ x
  intro r hr
  norm_num [PhaseCertificate3P17.weights] at hr
  interval_cases r
  · simpa [PhaseCertificate3P17.weights, PhaseSOS.weightScale] using weight_lower_1
  · simpa [PhaseCertificate3P17.weights, PhaseSOS.weightScale] using weight_lower_2
  · simpa [PhaseCertificate3P17.weights, PhaseSOS.weightScale] using weight_lower_3
  · simpa [PhaseCertificate3P17.weights, PhaseSOS.weightScale] using weight_lower_4
  · simpa [PhaseCertificate3P17.weights, PhaseSOS.weightScale] using weight_lower_5
  · simpa [PhaseCertificate3P17.weights, PhaseSOS.weightScale] using weight_lower_6
  · simpa [PhaseCertificate3P17.weights, PhaseSOS.weightScale] using weight_lower_7
  · simpa [PhaseCertificate3P17.weights, PhaseSOS.weightScale] using weight_lower_8
  · simpa [PhaseCertificate3P17.weights, PhaseSOS.weightScale] using weight_lower_9
  · simpa [PhaseCertificate3P17.weights, PhaseSOS.weightScale] using weight_lower_10

#print axioms phase_lower
end Varlamov.PhaseWeights3P17
