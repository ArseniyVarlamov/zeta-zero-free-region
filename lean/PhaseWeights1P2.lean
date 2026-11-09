import PrimeNumberTheoremAnd.IEANTN.Varlamov.PhaseWeightBridge
import PrimeNumberTheoremAnd.IEANTN.Varlamov.PhaseCertificate1P2

namespace Varlamov.PhaseWeights1P2
open Real
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000

lemma prime_selected : 2 ∈ selectedPrimes (0 : Fin 7) := by norm_num [selectedPrimes]

lemma weight_lower_1 : (3330794173590 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (0 : Fin 7) 2 1 := by
  rw [primeOmegaWeight_piece (0 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa1, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_2 : (2001410801755 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (0 : Fin 7) 2 2 := by
  rw [primeOmegaWeight_piece (0 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa1, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_3 : (1114658857761 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (0 : Fin 7) 2 3 := by
  rw [primeOmegaWeight_piece (0 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa1, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_4 : (591632849325 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (0 : Fin 7) 2 4 := by
  rw [primeOmegaWeight_piece (0 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa1, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_5 : (305461203426 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (0 : Fin 7) 2 5 := by
  rw [primeOmegaWeight_piece (0 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa1, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_6 : (155358462076 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (0 : Fin 7) 2 6 := by
  rw [primeOmegaWeight_piece (0 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa1, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_7 : (78389917110 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (0 : Fin 7) 2 7 := by
  rw [primeOmegaWeight_piece (0 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa1, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_8 : (39388325406 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (0 : Fin 7) 2 8 := by
  rw [primeOmegaWeight_piece (0 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa1, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_9 : (19747192582 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (0 : Fin 7) 2 9 := by
  rw [primeOmegaWeight_piece (0 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa1, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_10 : (9887994471 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (0 : Fin 7) 2 10 := by
  rw [primeOmegaWeight_piece (0 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa1, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

theorem phase_lower (x : ℝ) :
    (((PhaseCertificate1P2.target - 1 : ℤ) : ℝ) / PhaseSOS.targetScale) ≤ primePhase (0 : Fin 7) 2 x := by
  apply (PhaseCertificate1P2.rounded_lower_bound x).trans
  apply roundedPhase_le_primePhase (0 : Fin 7) 2 PhaseCertificate1P2.weights
    (by norm_num [PhaseCertificate1P2.weights, powerCount]) ?_ x
  intro r hr
  norm_num [PhaseCertificate1P2.weights] at hr
  interval_cases r
  · simpa [PhaseCertificate1P2.weights, PhaseSOS.weightScale] using weight_lower_1
  · simpa [PhaseCertificate1P2.weights, PhaseSOS.weightScale] using weight_lower_2
  · simpa [PhaseCertificate1P2.weights, PhaseSOS.weightScale] using weight_lower_3
  · simpa [PhaseCertificate1P2.weights, PhaseSOS.weightScale] using weight_lower_4
  · simpa [PhaseCertificate1P2.weights, PhaseSOS.weightScale] using weight_lower_5
  · simpa [PhaseCertificate1P2.weights, PhaseSOS.weightScale] using weight_lower_6
  · simpa [PhaseCertificate1P2.weights, PhaseSOS.weightScale] using weight_lower_7
  · simpa [PhaseCertificate1P2.weights, PhaseSOS.weightScale] using weight_lower_8
  · simpa [PhaseCertificate1P2.weights, PhaseSOS.weightScale] using weight_lower_9
  · simpa [PhaseCertificate1P2.weights, PhaseSOS.weightScale] using weight_lower_10

#print axioms phase_lower
end Varlamov.PhaseWeights1P2
