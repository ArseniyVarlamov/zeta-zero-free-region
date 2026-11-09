import PrimeNumberTheoremAnd.IEANTN.Varlamov.PhaseWeightBridge
import PrimeNumberTheoremAnd.IEANTN.Varlamov.PhaseCertificate1P13

namespace Varlamov.PhaseWeights1P13
open Real
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000

lemma prime_selected : 13 ∈ selectedPrimes (0 : Fin 7) := by norm_num [selectedPrimes]

lemma weight_lower_1 : (717875954646 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (0 : Fin 7) 13 1 := by
  rw [primeOmegaWeight_piece (0 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa1, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_2 : (59511159976 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (0 : Fin 7) 13 2 := by
  rw [primeOmegaWeight_piece (0 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa1, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_3 : (4612292974 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (0 : Fin 7) 13 3 := by
  rw [primeOmegaWeight_piece (0 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa1, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_4 : (354579862 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (0 : Fin 7) 13 4 := by
  rw [primeOmegaWeight_piece (0 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa1, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_5 : (27174168 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (0 : Fin 7) 13 5 := by
  rw [primeOmegaWeight_piece (0 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa1, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_6 : (2077006 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (0 : Fin 7) 13 6 := by
  rw [primeOmegaWeight_piece (0 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa1, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_7 : (158339 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (0 : Fin 7) 13 7 := by
  rw [primeOmegaWeight_piece (0 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa1, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_8 : (12039 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (0 : Fin 7) 13 8 := by
  rw [primeOmegaWeight_piece (0 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa1, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_9 : (912 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (0 : Fin 7) 13 9 := by
  rw [primeOmegaWeight_piece (0 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa1, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_10 : (68 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (0 : Fin 7) 13 10 := by
  rw [primeOmegaWeight_piece (0 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa1, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

theorem phase_lower (x : ℝ) :
    (((PhaseCertificate1P13.target - 1 : ℤ) : ℝ) / PhaseSOS.targetScale) ≤ primePhase (0 : Fin 7) 13 x := by
  apply (PhaseCertificate1P13.rounded_lower_bound x).trans
  apply roundedPhase_le_primePhase (0 : Fin 7) 13 PhaseCertificate1P13.weights
    (by norm_num [PhaseCertificate1P13.weights, powerCount]) ?_ x
  intro r hr
  norm_num [PhaseCertificate1P13.weights] at hr
  interval_cases r
  · simpa [PhaseCertificate1P13.weights, PhaseSOS.weightScale] using weight_lower_1
  · simpa [PhaseCertificate1P13.weights, PhaseSOS.weightScale] using weight_lower_2
  · simpa [PhaseCertificate1P13.weights, PhaseSOS.weightScale] using weight_lower_3
  · simpa [PhaseCertificate1P13.weights, PhaseSOS.weightScale] using weight_lower_4
  · simpa [PhaseCertificate1P13.weights, PhaseSOS.weightScale] using weight_lower_5
  · simpa [PhaseCertificate1P13.weights, PhaseSOS.weightScale] using weight_lower_6
  · simpa [PhaseCertificate1P13.weights, PhaseSOS.weightScale] using weight_lower_7
  · simpa [PhaseCertificate1P13.weights, PhaseSOS.weightScale] using weight_lower_8
  · simpa [PhaseCertificate1P13.weights, PhaseSOS.weightScale] using weight_lower_9
  · simpa [PhaseCertificate1P13.weights, PhaseSOS.weightScale] using weight_lower_10

#print axioms phase_lower
end Varlamov.PhaseWeights1P13
