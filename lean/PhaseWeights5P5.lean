import PrimeNumberTheoremAnd.IEANTN.Varlamov.PhaseWeightBridge
import PrimeNumberTheoremAnd.IEANTN.Varlamov.PhaseCertificate5P5

namespace Varlamov.PhaseWeights5P5
open Real
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000

lemma prime_selected : 5 ∈ selectedPrimes (4 : Fin 7) := by norm_num [selectedPrimes]

lemma weight_lower_1 : (1669605061253 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (4 : Fin 7) 5 1 := by
  rw [primeOmegaWeight_piece (4 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa5, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_2 : (386743547973 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (4 : Fin 7) 5 2 := by
  rw [primeOmegaWeight_piece (4 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa5, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_3 : (80066952689 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (4 : Fin 7) 5 3 := by
  rw [primeOmegaWeight_piece (4 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa5, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_4 : (16161255972 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (4 : Fin 7) 5 4 := by
  rw [primeOmegaWeight_piece (4 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa5, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_5 : (3244660527 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (4 : Fin 7) 5 5 := by
  rw [primeOmegaWeight_piece (4 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa5, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_6 : (650633363 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (4 : Fin 7) 5 6 := by
  rw [primeOmegaWeight_piece (4 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa5, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_7 : (130419332 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (4 : Fin 7) 5 7 := by
  rw [primeOmegaWeight_piece (4 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa5, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_8 : (26137284 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (4 : Fin 7) 5 8 := by
  rw [primeOmegaWeight_piece (4 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa5, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_9 : (5237296 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (4 : Fin 7) 5 9 := by
  rw [primeOmegaWeight_piece (4 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa5, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_10 : (1049265 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (4 : Fin 7) 5 10 := by
  rw [primeOmegaWeight_piece (4 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa5, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

theorem phase_lower (x : ℝ) :
    (((PhaseCertificate5P5.target - 1 : ℤ) : ℝ) / PhaseSOS.targetScale) ≤ primePhase (4 : Fin 7) 5 x := by
  apply (PhaseCertificate5P5.rounded_lower_bound x).trans
  apply roundedPhase_le_primePhase (4 : Fin 7) 5 PhaseCertificate5P5.weights
    (by norm_num [PhaseCertificate5P5.weights, powerCount]) ?_ x
  intro r hr
  norm_num [PhaseCertificate5P5.weights] at hr
  interval_cases r
  · simpa [PhaseCertificate5P5.weights, PhaseSOS.weightScale] using weight_lower_1
  · simpa [PhaseCertificate5P5.weights, PhaseSOS.weightScale] using weight_lower_2
  · simpa [PhaseCertificate5P5.weights, PhaseSOS.weightScale] using weight_lower_3
  · simpa [PhaseCertificate5P5.weights, PhaseSOS.weightScale] using weight_lower_4
  · simpa [PhaseCertificate5P5.weights, PhaseSOS.weightScale] using weight_lower_5
  · simpa [PhaseCertificate5P5.weights, PhaseSOS.weightScale] using weight_lower_6
  · simpa [PhaseCertificate5P5.weights, PhaseSOS.weightScale] using weight_lower_7
  · simpa [PhaseCertificate5P5.weights, PhaseSOS.weightScale] using weight_lower_8
  · simpa [PhaseCertificate5P5.weights, PhaseSOS.weightScale] using weight_lower_9
  · simpa [PhaseCertificate5P5.weights, PhaseSOS.weightScale] using weight_lower_10

#print axioms phase_lower
end Varlamov.PhaseWeights5P5
