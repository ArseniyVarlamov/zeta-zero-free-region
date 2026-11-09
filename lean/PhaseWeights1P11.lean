import PrimeNumberTheoremAnd.IEANTN.Varlamov.PhaseWeightBridge
import PrimeNumberTheoremAnd.IEANTN.Varlamov.PhaseCertificate1P11

namespace Varlamov.PhaseWeights1P11
open Real
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000

lemma prime_selected : 11 ∈ selectedPrimes (0 : Fin 7) := by norm_num [selectedPrimes]

lemma weight_lower_1 : (837003678321 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (0 : Fin 7) 11 1 := by
  rw [primeOmegaWeight_piece (0 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa1, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_2 : (82879521709 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (0 : Fin 7) 11 2 := by
  rw [primeOmegaWeight_piece (0 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa1, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_3 : (7609917738 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (0 : Fin 7) 11 3 := by
  rw [primeOmegaWeight_piece (0 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa1, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_4 : (692044951 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (0 : Fin 7) 11 4 := by
  rw [primeOmegaWeight_piece (0 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa1, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_5 : (62743051 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (0 : Fin 7) 11 5 := by
  rw [primeOmegaWeight_piece (0 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa1, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_6 : (5674946 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (0 : Fin 7) 11 6 := by
  rw [primeOmegaWeight_piece (0 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa1, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_7 : (512110 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (0 : Fin 7) 11 7 := by
  rw [primeOmegaWeight_piece (0 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa1, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_8 : (46108 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (0 : Fin 7) 11 8 := by
  rw [primeOmegaWeight_piece (0 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa1, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_9 : (4141 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (0 : Fin 7) 11 9 := by
  rw [primeOmegaWeight_piece (0 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa1, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_10 : (370 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (0 : Fin 7) 11 10 := by
  rw [primeOmegaWeight_piece (0 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa1, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

theorem phase_lower (x : ℝ) :
    (((PhaseCertificate1P11.target - 1 : ℤ) : ℝ) / PhaseSOS.targetScale) ≤ primePhase (0 : Fin 7) 11 x := by
  apply (PhaseCertificate1P11.rounded_lower_bound x).trans
  apply roundedPhase_le_primePhase (0 : Fin 7) 11 PhaseCertificate1P11.weights
    (by norm_num [PhaseCertificate1P11.weights, powerCount]) ?_ x
  intro r hr
  norm_num [PhaseCertificate1P11.weights] at hr
  interval_cases r
  · simpa [PhaseCertificate1P11.weights, PhaseSOS.weightScale] using weight_lower_1
  · simpa [PhaseCertificate1P11.weights, PhaseSOS.weightScale] using weight_lower_2
  · simpa [PhaseCertificate1P11.weights, PhaseSOS.weightScale] using weight_lower_3
  · simpa [PhaseCertificate1P11.weights, PhaseSOS.weightScale] using weight_lower_4
  · simpa [PhaseCertificate1P11.weights, PhaseSOS.weightScale] using weight_lower_5
  · simpa [PhaseCertificate1P11.weights, PhaseSOS.weightScale] using weight_lower_6
  · simpa [PhaseCertificate1P11.weights, PhaseSOS.weightScale] using weight_lower_7
  · simpa [PhaseCertificate1P11.weights, PhaseSOS.weightScale] using weight_lower_8
  · simpa [PhaseCertificate1P11.weights, PhaseSOS.weightScale] using weight_lower_9
  · simpa [PhaseCertificate1P11.weights, PhaseSOS.weightScale] using weight_lower_10

#print axioms phase_lower
end Varlamov.PhaseWeights1P11
