import PrimeNumberTheoremAnd.IEANTN.Varlamov.PhaseWeightBridge
import PrimeNumberTheoremAnd.IEANTN.Varlamov.PhaseCertificate7P83

namespace Varlamov.PhaseWeights7P83
open Real
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000

lemma prime_selected : 83 ∈ selectedPrimes (6 : Fin 7) := by norm_num [selectedPrimes]

lemma weight_lower_1 : (119988144873 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (6 : Fin 7) 83 1 := by
  rw [primeOmegaWeight_piece (6 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa7, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_2 : (1473557530 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (6 : Fin 7) 83 2 := by
  rw [primeOmegaWeight_piece (6 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa7, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_3 : (17862801 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (6 : Fin 7) 83 3 := by
  rw [primeOmegaWeight_piece (6 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa7, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_4 : (216278 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (6 : Fin 7) 83 4 := by
  rw [primeOmegaWeight_piece (6 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa7, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_5 : (2614 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (6 : Fin 7) 83 5 := by
  rw [primeOmegaWeight_piece (6 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa7, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_6 : (30 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (6 : Fin 7) 83 6 := by
  rw [primeOmegaWeight_piece (6 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa7, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_7 : (0 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (6 : Fin 7) 83 7 := by
  simpa only [zero_div] using (primeOmegaWeight_pos (6 : Fin 7) prime_selected (by norm_num [powerCount])).le

lemma weight_lower_8 : (0 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (6 : Fin 7) 83 8 := by
  simpa only [zero_div] using (primeOmegaWeight_pos (6 : Fin 7) prime_selected (by norm_num [powerCount])).le

lemma weight_lower_9 : (0 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (6 : Fin 7) 83 9 := by
  simpa only [zero_div] using (primeOmegaWeight_pos (6 : Fin 7) prime_selected (by norm_num [powerCount])).le

lemma weight_lower_10 : (0 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (6 : Fin 7) 83 10 := by
  simpa only [zero_div] using (primeOmegaWeight_pos (6 : Fin 7) prime_selected (by norm_num [powerCount])).le

lemma weight_lower_11 : (0 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (6 : Fin 7) 83 11 := by
  simpa only [zero_div] using (primeOmegaWeight_pos (6 : Fin 7) prime_selected (by norm_num [powerCount])).le

lemma weight_lower_12 : (0 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (6 : Fin 7) 83 12 := by
  simpa only [zero_div] using (primeOmegaWeight_pos (6 : Fin 7) prime_selected (by norm_num [powerCount])).le

lemma weight_lower_13 : (0 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (6 : Fin 7) 83 13 := by
  simpa only [zero_div] using (primeOmegaWeight_pos (6 : Fin 7) prime_selected (by norm_num [powerCount])).le

lemma weight_lower_14 : (0 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (6 : Fin 7) 83 14 := by
  simpa only [zero_div] using (primeOmegaWeight_pos (6 : Fin 7) prime_selected (by norm_num [powerCount])).le

lemma weight_lower_15 : (0 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (6 : Fin 7) 83 15 := by
  simpa only [zero_div] using (primeOmegaWeight_pos (6 : Fin 7) prime_selected (by norm_num [powerCount])).le

lemma weight_lower_16 : (0 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (6 : Fin 7) 83 16 := by
  simpa only [zero_div] using (primeOmegaWeight_pos (6 : Fin 7) prime_selected (by norm_num [powerCount])).le

lemma weight_lower_17 : (0 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (6 : Fin 7) 83 17 := by
  simpa only [zero_div] using (primeOmegaWeight_pos (6 : Fin 7) prime_selected (by norm_num [powerCount])).le

lemma weight_lower_18 : (0 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (6 : Fin 7) 83 18 := by
  simpa only [zero_div] using (primeOmegaWeight_pos (6 : Fin 7) prime_selected (by norm_num [powerCount])).le

lemma weight_lower_19 : (0 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (6 : Fin 7) 83 19 := by
  simpa only [zero_div] using (primeOmegaWeight_pos (6 : Fin 7) prime_selected (by norm_num [powerCount])).le

lemma weight_lower_20 : (0 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (6 : Fin 7) 83 20 := by
  simpa only [zero_div] using (primeOmegaWeight_pos (6 : Fin 7) prime_selected (by norm_num [powerCount])).le

theorem phase_lower (x : ℝ) :
    (((PhaseCertificate7P83.target - 1 : ℤ) : ℝ) / PhaseSOS.targetScale) ≤ primePhase (6 : Fin 7) 83 x := by
  apply (PhaseCertificate7P83.rounded_lower_bound x).trans
  apply roundedPhase_le_primePhase (6 : Fin 7) 83 PhaseCertificate7P83.weights
    (by norm_num [PhaseCertificate7P83.weights, powerCount]) ?_ x
  intro r hr
  norm_num [PhaseCertificate7P83.weights] at hr
  interval_cases r
  · simpa [PhaseCertificate7P83.weights, PhaseSOS.weightScale] using weight_lower_1
  · simpa [PhaseCertificate7P83.weights, PhaseSOS.weightScale] using weight_lower_2
  · simpa [PhaseCertificate7P83.weights, PhaseSOS.weightScale] using weight_lower_3
  · simpa [PhaseCertificate7P83.weights, PhaseSOS.weightScale] using weight_lower_4
  · simpa [PhaseCertificate7P83.weights, PhaseSOS.weightScale] using weight_lower_5
  · simpa [PhaseCertificate7P83.weights, PhaseSOS.weightScale] using weight_lower_6
  · simpa [PhaseCertificate7P83.weights, PhaseSOS.weightScale] using weight_lower_7
  · simpa [PhaseCertificate7P83.weights, PhaseSOS.weightScale] using weight_lower_8
  · simpa [PhaseCertificate7P83.weights, PhaseSOS.weightScale] using weight_lower_9
  · simpa [PhaseCertificate7P83.weights, PhaseSOS.weightScale] using weight_lower_10
  · simpa [PhaseCertificate7P83.weights, PhaseSOS.weightScale] using weight_lower_11
  · simpa [PhaseCertificate7P83.weights, PhaseSOS.weightScale] using weight_lower_12
  · simpa [PhaseCertificate7P83.weights, PhaseSOS.weightScale] using weight_lower_13
  · simpa [PhaseCertificate7P83.weights, PhaseSOS.weightScale] using weight_lower_14
  · simpa [PhaseCertificate7P83.weights, PhaseSOS.weightScale] using weight_lower_15
  · simpa [PhaseCertificate7P83.weights, PhaseSOS.weightScale] using weight_lower_16
  · simpa [PhaseCertificate7P83.weights, PhaseSOS.weightScale] using weight_lower_17
  · simpa [PhaseCertificate7P83.weights, PhaseSOS.weightScale] using weight_lower_18
  · simpa [PhaseCertificate7P83.weights, PhaseSOS.weightScale] using weight_lower_19
  · simpa [PhaseCertificate7P83.weights, PhaseSOS.weightScale] using weight_lower_20

#print axioms phase_lower
end Varlamov.PhaseWeights7P83
