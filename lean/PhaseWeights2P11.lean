import PrimeNumberTheoremAnd.IEANTN.Varlamov.PhaseWeightBridge
import PrimeNumberTheoremAnd.IEANTN.Varlamov.PhaseCertificate2P11

namespace Varlamov.PhaseWeights2P11
open Real
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000

lemma prime_selected : 11 ∈ selectedPrimes (1 : Fin 7) := by norm_num [selectedPrimes]

lemma weight_lower_1 : (836747569804 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (1 : Fin 7) 11 1 := by
  rw [primeOmegaWeight_piece (1 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa2, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_2 : (82815275724 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (1 : Fin 7) 11 2 := by
  rw [primeOmegaWeight_piece (1 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa2, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_3 : (7615960643 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (1 : Fin 7) 11 3 := by
  rw [primeOmegaWeight_piece (1 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa2, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_4 : (694754750 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (1 : Fin 7) 11 4 := by
  rw [primeOmegaWeight_piece (1 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa2, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_5 : (63272910 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (1 : Fin 7) 11 5 := by
  rw [primeOmegaWeight_piece (1 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa2, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_6 : (5756389 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (1 : Fin 7) 11 6 := by
  rw [primeOmegaWeight_piece (1 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa2, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_7 : (523189 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (1 : Fin 7) 11 7 := by
  rw [primeOmegaWeight_piece (1 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa2, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_8 : (47505 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (1 : Fin 7) 11 8 := by
  rw [primeOmegaWeight_piece (1 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa2, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_9 : (4308 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (1 : Fin 7) 11 9 := by
  rw [primeOmegaWeight_piece (1 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa2, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_10 : (389 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (1 : Fin 7) 11 10 := by
  rw [primeOmegaWeight_piece (1 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa2, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

theorem phase_lower (x : ℝ) :
    (((PhaseCertificate2P11.target - 1 : ℤ) : ℝ) / PhaseSOS.targetScale) ≤ primePhase (1 : Fin 7) 11 x := by
  apply (PhaseCertificate2P11.rounded_lower_bound x).trans
  apply roundedPhase_le_primePhase (1 : Fin 7) 11 PhaseCertificate2P11.weights
    (by norm_num [PhaseCertificate2P11.weights, powerCount]) ?_ x
  intro r hr
  norm_num [PhaseCertificate2P11.weights] at hr
  interval_cases r
  · simpa [PhaseCertificate2P11.weights, PhaseSOS.weightScale] using weight_lower_1
  · simpa [PhaseCertificate2P11.weights, PhaseSOS.weightScale] using weight_lower_2
  · simpa [PhaseCertificate2P11.weights, PhaseSOS.weightScale] using weight_lower_3
  · simpa [PhaseCertificate2P11.weights, PhaseSOS.weightScale] using weight_lower_4
  · simpa [PhaseCertificate2P11.weights, PhaseSOS.weightScale] using weight_lower_5
  · simpa [PhaseCertificate2P11.weights, PhaseSOS.weightScale] using weight_lower_6
  · simpa [PhaseCertificate2P11.weights, PhaseSOS.weightScale] using weight_lower_7
  · simpa [PhaseCertificate2P11.weights, PhaseSOS.weightScale] using weight_lower_8
  · simpa [PhaseCertificate2P11.weights, PhaseSOS.weightScale] using weight_lower_9
  · simpa [PhaseCertificate2P11.weights, PhaseSOS.weightScale] using weight_lower_10

#print axioms phase_lower
end Varlamov.PhaseWeights2P11
