import PrimeNumberTheoremAnd.IEANTN.Varlamov.PhaseWeightBridge
import PrimeNumberTheoremAnd.IEANTN.Varlamov.PhaseCertificate6P11

namespace Varlamov.PhaseWeights6P11
open Real
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000

lemma prime_selected : 11 ∈ selectedPrimes (5 : Fin 7) := by norm_num [selectedPrimes]

lemma weight_lower_1 : (836293849858 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (5 : Fin 7) 11 1 := by
  rw [primeOmegaWeight_piece (5 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa6, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_2 : (82673200004 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (5 : Fin 7) 11 2 := by
  rw [primeOmegaWeight_piece (5 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa6, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_3 : (7602932875 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (5 : Fin 7) 11 3 := by
  rw [primeOmegaWeight_piece (5 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa6, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_4 : (694124354 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (5 : Fin 7) 11 4 := by
  rw [primeOmegaWeight_piece (5 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa6, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_5 : (63309991 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (5 : Fin 7) 11 5 := by
  rw [primeOmegaWeight_piece (5 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa6, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_6 : (5772192 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (5 : Fin 7) 11 6 := by
  rw [primeOmegaWeight_piece (5 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa6, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_7 : (526098 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (5 : Fin 7) 11 7 := by
  rw [primeOmegaWeight_piece (5 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa6, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_8 : (47934 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (5 : Fin 7) 11 8 := by
  rw [primeOmegaWeight_piece (5 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa6, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_9 : (4365 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (5 : Fin 7) 11 9 := by
  rw [primeOmegaWeight_piece (5 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa6, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_10 : (396 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (5 : Fin 7) 11 10 := by
  rw [primeOmegaWeight_piece (5 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa6, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

theorem phase_lower (x : ℝ) :
    (((PhaseCertificate6P11.target - 1 : ℤ) : ℝ) / PhaseSOS.targetScale) ≤ primePhase (5 : Fin 7) 11 x := by
  apply (PhaseCertificate6P11.rounded_lower_bound x).trans
  apply roundedPhase_le_primePhase (5 : Fin 7) 11 PhaseCertificate6P11.weights
    (by norm_num [PhaseCertificate6P11.weights, powerCount]) ?_ x
  intro r hr
  norm_num [PhaseCertificate6P11.weights] at hr
  interval_cases r
  · simpa [PhaseCertificate6P11.weights, PhaseSOS.weightScale] using weight_lower_1
  · simpa [PhaseCertificate6P11.weights, PhaseSOS.weightScale] using weight_lower_2
  · simpa [PhaseCertificate6P11.weights, PhaseSOS.weightScale] using weight_lower_3
  · simpa [PhaseCertificate6P11.weights, PhaseSOS.weightScale] using weight_lower_4
  · simpa [PhaseCertificate6P11.weights, PhaseSOS.weightScale] using weight_lower_5
  · simpa [PhaseCertificate6P11.weights, PhaseSOS.weightScale] using weight_lower_6
  · simpa [PhaseCertificate6P11.weights, PhaseSOS.weightScale] using weight_lower_7
  · simpa [PhaseCertificate6P11.weights, PhaseSOS.weightScale] using weight_lower_8
  · simpa [PhaseCertificate6P11.weights, PhaseSOS.weightScale] using weight_lower_9
  · simpa [PhaseCertificate6P11.weights, PhaseSOS.weightScale] using weight_lower_10

#print axioms phase_lower
end Varlamov.PhaseWeights6P11
