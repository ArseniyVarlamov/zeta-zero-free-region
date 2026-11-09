import PrimeNumberTheoremAnd.IEANTN.Varlamov.PhaseWeightBridge
import PrimeNumberTheoremAnd.IEANTN.Varlamov.PhaseCertificate6P3

namespace Varlamov.PhaseWeights6P3
open Real
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000

lemma prime_selected : 3 ∈ selectedPrimes (5 : Fin 7) := by norm_num [selectedPrimes]

lemma weight_lower_1 : (2501863031042 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (5 : Fin 7) 3 1 := by
  rw [primeOmegaWeight_piece (5 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa6, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_2 : (1003082546523 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (5 : Fin 7) 3 2 := by
  rw [primeOmegaWeight_piece (5 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa6, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_3 : (359141332117 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (5 : Fin 7) 3 3 := by
  rw [primeOmegaWeight_piece (5 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa6, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_4 : (122908770964 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (5 : Fin 7) 3 4 := by
  rw [primeOmegaWeight_piece (5 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa6, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_5 : (41388245211 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (5 : Fin 7) 3 5 := by
  rw [primeOmegaWeight_piece (5 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa6, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_6 : (13859413246 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (5 : Fin 7) 3 6 := by
  rw [primeOmegaWeight_piece (5 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa6, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_7 : (4632050841 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (5 : Fin 7) 3 7 := by
  rw [primeOmegaWeight_piece (5 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa6, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_8 : (1547033703 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (5 : Fin 7) 3 8 := by
  rw [primeOmegaWeight_piece (5 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa6, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_9 : (516541284 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (5 : Fin 7) 3 9 := by
  rw [primeOmegaWeight_piece (5 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa6, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_10 : (172444714 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (5 : Fin 7) 3 10 := by
  rw [primeOmegaWeight_piece (5 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa6, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

theorem phase_lower (x : ℝ) :
    (((PhaseCertificate6P3.target - 1 : ℤ) : ℝ) / PhaseSOS.targetScale) ≤ primePhase (5 : Fin 7) 3 x := by
  apply (PhaseCertificate6P3.rounded_lower_bound x).trans
  apply roundedPhase_le_primePhase (5 : Fin 7) 3 PhaseCertificate6P3.weights
    (by norm_num [PhaseCertificate6P3.weights, powerCount]) ?_ x
  intro r hr
  norm_num [PhaseCertificate6P3.weights] at hr
  interval_cases r
  · simpa [PhaseCertificate6P3.weights, PhaseSOS.weightScale] using weight_lower_1
  · simpa [PhaseCertificate6P3.weights, PhaseSOS.weightScale] using weight_lower_2
  · simpa [PhaseCertificate6P3.weights, PhaseSOS.weightScale] using weight_lower_3
  · simpa [PhaseCertificate6P3.weights, PhaseSOS.weightScale] using weight_lower_4
  · simpa [PhaseCertificate6P3.weights, PhaseSOS.weightScale] using weight_lower_5
  · simpa [PhaseCertificate6P3.weights, PhaseSOS.weightScale] using weight_lower_6
  · simpa [PhaseCertificate6P3.weights, PhaseSOS.weightScale] using weight_lower_7
  · simpa [PhaseCertificate6P3.weights, PhaseSOS.weightScale] using weight_lower_8
  · simpa [PhaseCertificate6P3.weights, PhaseSOS.weightScale] using weight_lower_9
  · simpa [PhaseCertificate6P3.weights, PhaseSOS.weightScale] using weight_lower_10

#print axioms phase_lower
end Varlamov.PhaseWeights6P3
