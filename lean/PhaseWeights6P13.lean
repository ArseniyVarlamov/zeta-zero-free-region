import PrimeNumberTheoremAnd.IEANTN.Varlamov.PhaseWeightBridge
import PrimeNumberTheoremAnd.IEANTN.Varlamov.PhaseCertificate6P13

namespace Varlamov.PhaseWeights6P13
open Real
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000

lemma prime_selected : 13 ∈ selectedPrimes (5 : Fin 7) := by norm_num [selectedPrimes]

lemma weight_lower_1 : (717101901183 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (5 : Fin 7) 13 1 := by
  rw [primeOmegaWeight_piece (5 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa6, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_2 : (59366222319 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (5 : Fin 7) 13 2 := by
  rw [primeOmegaWeight_piece (5 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa6, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_3 : (4611009221 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (5 : Fin 7) 13 3 := by
  rw [primeOmegaWeight_piece (5 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa6, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_4 : (356167208 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (5 : Fin 7) 13 4 := by
  rw [primeOmegaWeight_piece (5 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa6, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_5 : (27490007 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (5 : Fin 7) 13 5 := by
  rw [primeOmegaWeight_piece (5 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa6, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_6 : (2120907 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (5 : Fin 7) 13 6 := by
  rw [primeOmegaWeight_piece (5 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa6, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_7 : (163571 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (5 : Fin 7) 13 7 := by
  rw [primeOmegaWeight_piece (5 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa6, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_8 : (12609 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (5 : Fin 7) 13 8 := by
  rw [primeOmegaWeight_piece (5 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa6, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_9 : (970 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (5 : Fin 7) 13 9 := by
  rw [primeOmegaWeight_piece (5 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa6, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_10 : (73 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (5 : Fin 7) 13 10 := by
  rw [primeOmegaWeight_piece (5 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa6, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

theorem phase_lower (x : ℝ) :
    (((PhaseCertificate6P13.target - 1 : ℤ) : ℝ) / PhaseSOS.targetScale) ≤ primePhase (5 : Fin 7) 13 x := by
  apply (PhaseCertificate6P13.rounded_lower_bound x).trans
  apply roundedPhase_le_primePhase (5 : Fin 7) 13 PhaseCertificate6P13.weights
    (by norm_num [PhaseCertificate6P13.weights, powerCount]) ?_ x
  intro r hr
  norm_num [PhaseCertificate6P13.weights] at hr
  interval_cases r
  · simpa [PhaseCertificate6P13.weights, PhaseSOS.weightScale] using weight_lower_1
  · simpa [PhaseCertificate6P13.weights, PhaseSOS.weightScale] using weight_lower_2
  · simpa [PhaseCertificate6P13.weights, PhaseSOS.weightScale] using weight_lower_3
  · simpa [PhaseCertificate6P13.weights, PhaseSOS.weightScale] using weight_lower_4
  · simpa [PhaseCertificate6P13.weights, PhaseSOS.weightScale] using weight_lower_5
  · simpa [PhaseCertificate6P13.weights, PhaseSOS.weightScale] using weight_lower_6
  · simpa [PhaseCertificate6P13.weights, PhaseSOS.weightScale] using weight_lower_7
  · simpa [PhaseCertificate6P13.weights, PhaseSOS.weightScale] using weight_lower_8
  · simpa [PhaseCertificate6P13.weights, PhaseSOS.weightScale] using weight_lower_9
  · simpa [PhaseCertificate6P13.weights, PhaseSOS.weightScale] using weight_lower_10

#print axioms phase_lower
end Varlamov.PhaseWeights6P13
