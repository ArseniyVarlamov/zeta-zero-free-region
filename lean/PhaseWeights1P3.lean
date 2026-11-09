import PrimeNumberTheoremAnd.IEANTN.Varlamov.PhaseWeightBridge
import PrimeNumberTheoremAnd.IEANTN.Varlamov.PhaseCertificate1P3

namespace Varlamov.PhaseWeights1P3
open Real
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000

lemma prime_selected : 3 ∈ selectedPrimes (0 : Fin 7) := by norm_num [selectedPrimes]

lemma weight_lower_1 : (2499757276794 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (0 : Fin 7) 3 1 := by
  rw [primeOmegaWeight_piece (0 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa1, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_2 : (1003642872933 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (0 : Fin 7) 3 2 := by
  rw [primeOmegaWeight_piece (0 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa1, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_3 : (359825519063 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (0 : Fin 7) 3 3 := by
  rw [primeOmegaWeight_piece (0 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa1, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_4 : (123213253969 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (0 : Fin 7) 3 4 := by
  rw [primeOmegaWeight_piece (0 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa1, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_5 : (41484096622 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (0 : Fin 7) 3 5 := by
  rw [primeOmegaWeight_piece (0 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa1, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_6 : (13880973029 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (0 : Fin 7) 3 6 := by
  rw [primeOmegaWeight_piece (0 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa1, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_7 : (4633369480 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (0 : Fin 7) 3 7 := by
  rw [primeOmegaWeight_piece (0 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa1, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_8 : (1544790592 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (0 : Fin 7) 3 8 := by
  rw [primeOmegaWeight_piece (0 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa1, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_9 : (514669635 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (0 : Fin 7) 3 9 := by
  rw [primeOmegaWeight_piece (0 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa1, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_10 : (171371932 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (0 : Fin 7) 3 10 := by
  rw [primeOmegaWeight_piece (0 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa1, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

theorem phase_lower (x : ℝ) :
    (((PhaseCertificate1P3.target - 1 : ℤ) : ℝ) / PhaseSOS.targetScale) ≤ primePhase (0 : Fin 7) 3 x := by
  apply (PhaseCertificate1P3.rounded_lower_bound x).trans
  apply roundedPhase_le_primePhase (0 : Fin 7) 3 PhaseCertificate1P3.weights
    (by norm_num [PhaseCertificate1P3.weights, powerCount]) ?_ x
  intro r hr
  norm_num [PhaseCertificate1P3.weights] at hr
  interval_cases r
  · simpa [PhaseCertificate1P3.weights, PhaseSOS.weightScale] using weight_lower_1
  · simpa [PhaseCertificate1P3.weights, PhaseSOS.weightScale] using weight_lower_2
  · simpa [PhaseCertificate1P3.weights, PhaseSOS.weightScale] using weight_lower_3
  · simpa [PhaseCertificate1P3.weights, PhaseSOS.weightScale] using weight_lower_4
  · simpa [PhaseCertificate1P3.weights, PhaseSOS.weightScale] using weight_lower_5
  · simpa [PhaseCertificate1P3.weights, PhaseSOS.weightScale] using weight_lower_6
  · simpa [PhaseCertificate1P3.weights, PhaseSOS.weightScale] using weight_lower_7
  · simpa [PhaseCertificate1P3.weights, PhaseSOS.weightScale] using weight_lower_8
  · simpa [PhaseCertificate1P3.weights, PhaseSOS.weightScale] using weight_lower_9
  · simpa [PhaseCertificate1P3.weights, PhaseSOS.weightScale] using weight_lower_10

#print axioms phase_lower
end Varlamov.PhaseWeights1P3
