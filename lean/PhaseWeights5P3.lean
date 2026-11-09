import PrimeNumberTheoremAnd.IEANTN.Varlamov.PhaseWeightBridge
import PrimeNumberTheoremAnd.IEANTN.Varlamov.PhaseCertificate5P3

namespace Varlamov.PhaseWeights5P3
open Real
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000

lemma prime_selected : 3 ∈ selectedPrimes (4 : Fin 7) := by norm_num [selectedPrimes]

lemma weight_lower_1 : (2501856164670 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (4 : Fin 7) 3 1 := by
  rw [primeOmegaWeight_piece (4 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa5, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_2 : (1003134152463 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (4 : Fin 7) 3 2 := by
  rw [primeOmegaWeight_piece (4 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa5, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_3 : (359180569110 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (4 : Fin 7) 3 3 := by
  rw [primeOmegaWeight_piece (4 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa5, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_4 : (122927738133 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (4 : Fin 7) 3 4 := by
  rw [primeOmegaWeight_piece (4 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa5, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_5 : (41396006578 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (4 : Fin 7) 3 5 := by
  rw [primeOmegaWeight_piece (4 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa5, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_6 : (13862349344 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (4 : Fin 7) 3 6 := by
  rw [primeOmegaWeight_piece (4 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa5, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_7 : (4633112405 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (4 : Fin 7) 3 7 := by
  rw [primeOmegaWeight_piece (4 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa5, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_8 : (1547405691 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (4 : Fin 7) 3 8 := by
  rw [primeOmegaWeight_piece (4 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa5, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_9 : (516668407 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (4 : Fin 7) 3 9 := by
  rw [primeOmegaWeight_piece (4 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa5, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_10 : (172487194 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (4 : Fin 7) 3 10 := by
  rw [primeOmegaWeight_piece (4 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa5, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

theorem phase_lower (x : ℝ) :
    (((PhaseCertificate5P3.target - 1 : ℤ) : ℝ) / PhaseSOS.targetScale) ≤ primePhase (4 : Fin 7) 3 x := by
  apply (PhaseCertificate5P3.rounded_lower_bound x).trans
  apply roundedPhase_le_primePhase (4 : Fin 7) 3 PhaseCertificate5P3.weights
    (by norm_num [PhaseCertificate5P3.weights, powerCount]) ?_ x
  intro r hr
  norm_num [PhaseCertificate5P3.weights] at hr
  interval_cases r
  · simpa [PhaseCertificate5P3.weights, PhaseSOS.weightScale] using weight_lower_1
  · simpa [PhaseCertificate5P3.weights, PhaseSOS.weightScale] using weight_lower_2
  · simpa [PhaseCertificate5P3.weights, PhaseSOS.weightScale] using weight_lower_3
  · simpa [PhaseCertificate5P3.weights, PhaseSOS.weightScale] using weight_lower_4
  · simpa [PhaseCertificate5P3.weights, PhaseSOS.weightScale] using weight_lower_5
  · simpa [PhaseCertificate5P3.weights, PhaseSOS.weightScale] using weight_lower_6
  · simpa [PhaseCertificate5P3.weights, PhaseSOS.weightScale] using weight_lower_7
  · simpa [PhaseCertificate5P3.weights, PhaseSOS.weightScale] using weight_lower_8
  · simpa [PhaseCertificate5P3.weights, PhaseSOS.weightScale] using weight_lower_9
  · simpa [PhaseCertificate5P3.weights, PhaseSOS.weightScale] using weight_lower_10

#print axioms phase_lower
end Varlamov.PhaseWeights5P3
