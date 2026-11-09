import PrimeNumberTheoremAnd.IEANTN.Varlamov.PhaseWeightBridge
import PrimeNumberTheoremAnd.IEANTN.Varlamov.PhaseCertificate2P2

namespace Varlamov.PhaseWeights2P2
open Real
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000

lemma prime_selected : 2 ∈ selectedPrimes (1 : Fin 7) := by norm_num [selectedPrimes]

lemma weight_lower_1 : (3332593473591 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (1 : Fin 7) 2 1 := by
  rw [primeOmegaWeight_piece (1 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa2, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_2 : (2002160263205 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (1 : Fin 7) 2 2 := by
  rw [primeOmegaWeight_piece (1 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa2, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_3 : (1114560911156 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (1 : Fin 7) 2 3 := by
  rw [primeOmegaWeight_piece (1 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa2, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_4 : (591319450730 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (1 : Fin 7) 2 4 := by
  rw [primeOmegaWeight_piece (1 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa2, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_5 : (305215706467 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (1 : Fin 7) 2 5 := by
  rw [primeOmegaWeight_piece (1 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa2, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_6 : (155222304755 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (1 : Fin 7) 2 6 := by
  rw [primeOmegaWeight_piece (1 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa2, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_7 : (78330414203 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (1 : Fin 7) 2 7 := by
  rw [primeOmegaWeight_piece (1 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa2, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_8 : (39369720402 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (1 : Fin 7) 2 8 := by
  rw [primeOmegaWeight_piece (1 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa2, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_9 : (19746514527 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (1 : Fin 7) 2 9 := by
  rw [primeOmegaWeight_piece (1 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa2, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_10 : (9893353154 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (1 : Fin 7) 2 10 := by
  rw [primeOmegaWeight_piece (1 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa2, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

theorem phase_lower (x : ℝ) :
    (((PhaseCertificate2P2.target - 1 : ℤ) : ℝ) / PhaseSOS.targetScale) ≤ primePhase (1 : Fin 7) 2 x := by
  apply (PhaseCertificate2P2.rounded_lower_bound x).trans
  apply roundedPhase_le_primePhase (1 : Fin 7) 2 PhaseCertificate2P2.weights
    (by norm_num [PhaseCertificate2P2.weights, powerCount]) ?_ x
  intro r hr
  norm_num [PhaseCertificate2P2.weights] at hr
  interval_cases r
  · simpa [PhaseCertificate2P2.weights, PhaseSOS.weightScale] using weight_lower_1
  · simpa [PhaseCertificate2P2.weights, PhaseSOS.weightScale] using weight_lower_2
  · simpa [PhaseCertificate2P2.weights, PhaseSOS.weightScale] using weight_lower_3
  · simpa [PhaseCertificate2P2.weights, PhaseSOS.weightScale] using weight_lower_4
  · simpa [PhaseCertificate2P2.weights, PhaseSOS.weightScale] using weight_lower_5
  · simpa [PhaseCertificate2P2.weights, PhaseSOS.weightScale] using weight_lower_6
  · simpa [PhaseCertificate2P2.weights, PhaseSOS.weightScale] using weight_lower_7
  · simpa [PhaseCertificate2P2.weights, PhaseSOS.weightScale] using weight_lower_8
  · simpa [PhaseCertificate2P2.weights, PhaseSOS.weightScale] using weight_lower_9
  · simpa [PhaseCertificate2P2.weights, PhaseSOS.weightScale] using weight_lower_10

#print axioms phase_lower
end Varlamov.PhaseWeights2P2
