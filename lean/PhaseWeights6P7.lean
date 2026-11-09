import PrimeNumberTheoremAnd.IEANTN.Varlamov.PhaseWeightBridge
import PrimeNumberTheoremAnd.IEANTN.Varlamov.PhaseCertificate6P7

namespace Varlamov.PhaseWeights6P7
open Real
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000

lemma prime_selected : 7 ∈ selectedPrimes (5 : Fin 7) := by norm_num [selectedPrimes]

lemma weight_lower_1 : (1253122674776 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (5 : Fin 7) 7 1 := by
  rw [primeOmegaWeight_piece (5 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa6, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_2 : (201370753322 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (5 : Fin 7) 7 2 := by
  rw [primeOmegaWeight_piece (5 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa6, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_3 : (29374184877 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (5 : Fin 7) 7 3 := by
  rw [primeOmegaWeight_piece (5 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa6, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_4 : (4219974135 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (5 : Fin 7) 7 4 := by
  rw [primeOmegaWeight_piece (5 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa6, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_5 : (604792194 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (5 : Fin 7) 7 5 := by
  rw [primeOmegaWeight_piece (5 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa6, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_6 : (86630570 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (5 : Fin 7) 7 6 := by
  rw [primeOmegaWeight_piece (5 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa6, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_7 : (12405762 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (5 : Fin 7) 7 7 := by
  rw [primeOmegaWeight_piece (5 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa6, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_8 : (1776154 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (5 : Fin 7) 7 8 := by
  rw [primeOmegaWeight_piece (5 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa6, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_9 : (254240 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (5 : Fin 7) 7 9 := by
  rw [primeOmegaWeight_piece (5 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa6, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_10 : (36384 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (5 : Fin 7) 7 10 := by
  rw [primeOmegaWeight_piece (5 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa6, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

theorem phase_lower (x : ℝ) :
    (((PhaseCertificate6P7.target - 1 : ℤ) : ℝ) / PhaseSOS.targetScale) ≤ primePhase (5 : Fin 7) 7 x := by
  apply (PhaseCertificate6P7.rounded_lower_bound x).trans
  apply roundedPhase_le_primePhase (5 : Fin 7) 7 PhaseCertificate6P7.weights
    (by norm_num [PhaseCertificate6P7.weights, powerCount]) ?_ x
  intro r hr
  norm_num [PhaseCertificate6P7.weights] at hr
  interval_cases r
  · simpa [PhaseCertificate6P7.weights, PhaseSOS.weightScale] using weight_lower_1
  · simpa [PhaseCertificate6P7.weights, PhaseSOS.weightScale] using weight_lower_2
  · simpa [PhaseCertificate6P7.weights, PhaseSOS.weightScale] using weight_lower_3
  · simpa [PhaseCertificate6P7.weights, PhaseSOS.weightScale] using weight_lower_4
  · simpa [PhaseCertificate6P7.weights, PhaseSOS.weightScale] using weight_lower_5
  · simpa [PhaseCertificate6P7.weights, PhaseSOS.weightScale] using weight_lower_6
  · simpa [PhaseCertificate6P7.weights, PhaseSOS.weightScale] using weight_lower_7
  · simpa [PhaseCertificate6P7.weights, PhaseSOS.weightScale] using weight_lower_8
  · simpa [PhaseCertificate6P7.weights, PhaseSOS.weightScale] using weight_lower_9
  · simpa [PhaseCertificate6P7.weights, PhaseSOS.weightScale] using weight_lower_10

#print axioms phase_lower
end Varlamov.PhaseWeights6P7
