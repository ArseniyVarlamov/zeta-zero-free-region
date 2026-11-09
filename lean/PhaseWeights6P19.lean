import PrimeNumberTheoremAnd.IEANTN.Varlamov.PhaseWeightBridge
import PrimeNumberTheoremAnd.IEANTN.Varlamov.PhaseCertificate6P19

namespace Varlamov.PhaseWeights6P19
open Real
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000

lemma prime_selected : 19 ∈ selectedPrimes (5 : Fin 7) := by norm_num [selectedPrimes]

lemma weight_lower_1 : (502407254115 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (5 : Fin 7) 19 1 := by
  rw [primeOmegaWeight_piece (5 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa6, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_2 : (27916012053 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (5 : Fin 7) 19 2 := by
  rw [primeOmegaWeight_piece (5 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa6, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_3 : (1479926327 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (5 : Fin 7) 19 3 := by
  rw [primeOmegaWeight_piece (5 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa6, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_4 : (78217284 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (5 : Fin 7) 19 4 := by
  rw [primeOmegaWeight_piece (5 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa6, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_5 : (4131365 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (5 : Fin 7) 19 5 := by
  rw [primeOmegaWeight_piece (5 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa6, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_6 : (218107 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (5 : Fin 7) 19 6 := by
  rw [primeOmegaWeight_piece (5 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa6, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_7 : (11508 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (5 : Fin 7) 19 7 := by
  rw [primeOmegaWeight_piece (5 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa6, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_8 : (606 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (5 : Fin 7) 19 8 := by
  rw [primeOmegaWeight_piece (5 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa6, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_9 : (31 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (5 : Fin 7) 19 9 := by
  rw [primeOmegaWeight_piece (5 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa6, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_10 : (0 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (5 : Fin 7) 19 10 := by
  simpa only [zero_div] using (primeOmegaWeight_pos (5 : Fin 7) prime_selected (by norm_num [powerCount])).le

theorem phase_lower (x : ℝ) :
    (((PhaseCertificate6P19.target - 1 : ℤ) : ℝ) / PhaseSOS.targetScale) ≤ primePhase (5 : Fin 7) 19 x := by
  apply (PhaseCertificate6P19.rounded_lower_bound x).trans
  apply roundedPhase_le_primePhase (5 : Fin 7) 19 PhaseCertificate6P19.weights
    (by norm_num [PhaseCertificate6P19.weights, powerCount]) ?_ x
  intro r hr
  norm_num [PhaseCertificate6P19.weights] at hr
  interval_cases r
  · simpa [PhaseCertificate6P19.weights, PhaseSOS.weightScale] using weight_lower_1
  · simpa [PhaseCertificate6P19.weights, PhaseSOS.weightScale] using weight_lower_2
  · simpa [PhaseCertificate6P19.weights, PhaseSOS.weightScale] using weight_lower_3
  · simpa [PhaseCertificate6P19.weights, PhaseSOS.weightScale] using weight_lower_4
  · simpa [PhaseCertificate6P19.weights, PhaseSOS.weightScale] using weight_lower_5
  · simpa [PhaseCertificate6P19.weights, PhaseSOS.weightScale] using weight_lower_6
  · simpa [PhaseCertificate6P19.weights, PhaseSOS.weightScale] using weight_lower_7
  · simpa [PhaseCertificate6P19.weights, PhaseSOS.weightScale] using weight_lower_8
  · simpa [PhaseCertificate6P19.weights, PhaseSOS.weightScale] using weight_lower_9
  · simpa [PhaseCertificate6P19.weights, PhaseSOS.weightScale] using weight_lower_10

#print axioms phase_lower
end Varlamov.PhaseWeights6P19
