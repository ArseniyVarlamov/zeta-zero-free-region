import PrimeNumberTheoremAnd.IEANTN.Varlamov.PhaseWeightBridge
import PrimeNumberTheoremAnd.IEANTN.Varlamov.PhaseCertificate7P89

namespace Varlamov.PhaseWeights7P89
open Real
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000

lemma prime_selected : 89 ∈ selectedPrimes (6 : Fin 7) := by norm_num [selectedPrimes]

lemma weight_lower_1 : (112003846939 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (6 : Fin 7) 89 1 := by
  rw [primeOmegaWeight_piece (6 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa7, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_2 : (1281860661 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (6 : Fin 7) 89 2 := by
  rw [primeOmegaWeight_piece (6 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa7, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_3 : (14491911 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (6 : Fin 7) 89 3 := by
  rw [primeOmegaWeight_piece (6 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa7, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_4 : (163638 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (6 : Fin 7) 89 4 := by
  rw [primeOmegaWeight_piece (6 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa7, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_5 : (1844 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (6 : Fin 7) 89 5 := by
  rw [primeOmegaWeight_piece (6 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa7, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_6 : (19 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (6 : Fin 7) 89 6 := by
  rw [primeOmegaWeight_piece (6 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa7, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_7 : (0 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (6 : Fin 7) 89 7 := by
  simpa only [zero_div] using (primeOmegaWeight_pos (6 : Fin 7) prime_selected (by norm_num [powerCount])).le

lemma weight_lower_8 : (0 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (6 : Fin 7) 89 8 := by
  simpa only [zero_div] using (primeOmegaWeight_pos (6 : Fin 7) prime_selected (by norm_num [powerCount])).le

lemma weight_lower_9 : (0 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (6 : Fin 7) 89 9 := by
  simpa only [zero_div] using (primeOmegaWeight_pos (6 : Fin 7) prime_selected (by norm_num [powerCount])).le

lemma weight_lower_10 : (0 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (6 : Fin 7) 89 10 := by
  simpa only [zero_div] using (primeOmegaWeight_pos (6 : Fin 7) prime_selected (by norm_num [powerCount])).le

lemma weight_lower_11 : (0 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (6 : Fin 7) 89 11 := by
  simpa only [zero_div] using (primeOmegaWeight_pos (6 : Fin 7) prime_selected (by norm_num [powerCount])).le

lemma weight_lower_12 : (0 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (6 : Fin 7) 89 12 := by
  simpa only [zero_div] using (primeOmegaWeight_pos (6 : Fin 7) prime_selected (by norm_num [powerCount])).le

lemma weight_lower_13 : (0 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (6 : Fin 7) 89 13 := by
  simpa only [zero_div] using (primeOmegaWeight_pos (6 : Fin 7) prime_selected (by norm_num [powerCount])).le

lemma weight_lower_14 : (0 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (6 : Fin 7) 89 14 := by
  simpa only [zero_div] using (primeOmegaWeight_pos (6 : Fin 7) prime_selected (by norm_num [powerCount])).le

lemma weight_lower_15 : (0 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (6 : Fin 7) 89 15 := by
  simpa only [zero_div] using (primeOmegaWeight_pos (6 : Fin 7) prime_selected (by norm_num [powerCount])).le

lemma weight_lower_16 : (0 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (6 : Fin 7) 89 16 := by
  simpa only [zero_div] using (primeOmegaWeight_pos (6 : Fin 7) prime_selected (by norm_num [powerCount])).le

lemma weight_lower_17 : (0 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (6 : Fin 7) 89 17 := by
  simpa only [zero_div] using (primeOmegaWeight_pos (6 : Fin 7) prime_selected (by norm_num [powerCount])).le

lemma weight_lower_18 : (0 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (6 : Fin 7) 89 18 := by
  simpa only [zero_div] using (primeOmegaWeight_pos (6 : Fin 7) prime_selected (by norm_num [powerCount])).le

lemma weight_lower_19 : (0 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (6 : Fin 7) 89 19 := by
  simpa only [zero_div] using (primeOmegaWeight_pos (6 : Fin 7) prime_selected (by norm_num [powerCount])).le

lemma weight_lower_20 : (0 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (6 : Fin 7) 89 20 := by
  simpa only [zero_div] using (primeOmegaWeight_pos (6 : Fin 7) prime_selected (by norm_num [powerCount])).le

theorem phase_lower (x : ℝ) :
    (((PhaseCertificate7P89.target - 1 : ℤ) : ℝ) / PhaseSOS.targetScale) ≤ primePhase (6 : Fin 7) 89 x := by
  apply (PhaseCertificate7P89.rounded_lower_bound x).trans
  apply roundedPhase_le_primePhase (6 : Fin 7) 89 PhaseCertificate7P89.weights
    (by norm_num [PhaseCertificate7P89.weights, powerCount]) ?_ x
  intro r hr
  norm_num [PhaseCertificate7P89.weights] at hr
  interval_cases r
  · simpa [PhaseCertificate7P89.weights, PhaseSOS.weightScale] using weight_lower_1
  · simpa [PhaseCertificate7P89.weights, PhaseSOS.weightScale] using weight_lower_2
  · simpa [PhaseCertificate7P89.weights, PhaseSOS.weightScale] using weight_lower_3
  · simpa [PhaseCertificate7P89.weights, PhaseSOS.weightScale] using weight_lower_4
  · simpa [PhaseCertificate7P89.weights, PhaseSOS.weightScale] using weight_lower_5
  · simpa [PhaseCertificate7P89.weights, PhaseSOS.weightScale] using weight_lower_6
  · simpa [PhaseCertificate7P89.weights, PhaseSOS.weightScale] using weight_lower_7
  · simpa [PhaseCertificate7P89.weights, PhaseSOS.weightScale] using weight_lower_8
  · simpa [PhaseCertificate7P89.weights, PhaseSOS.weightScale] using weight_lower_9
  · simpa [PhaseCertificate7P89.weights, PhaseSOS.weightScale] using weight_lower_10
  · simpa [PhaseCertificate7P89.weights, PhaseSOS.weightScale] using weight_lower_11
  · simpa [PhaseCertificate7P89.weights, PhaseSOS.weightScale] using weight_lower_12
  · simpa [PhaseCertificate7P89.weights, PhaseSOS.weightScale] using weight_lower_13
  · simpa [PhaseCertificate7P89.weights, PhaseSOS.weightScale] using weight_lower_14
  · simpa [PhaseCertificate7P89.weights, PhaseSOS.weightScale] using weight_lower_15
  · simpa [PhaseCertificate7P89.weights, PhaseSOS.weightScale] using weight_lower_16
  · simpa [PhaseCertificate7P89.weights, PhaseSOS.weightScale] using weight_lower_17
  · simpa [PhaseCertificate7P89.weights, PhaseSOS.weightScale] using weight_lower_18
  · simpa [PhaseCertificate7P89.weights, PhaseSOS.weightScale] using weight_lower_19
  · simpa [PhaseCertificate7P89.weights, PhaseSOS.weightScale] using weight_lower_20

#print axioms phase_lower
end Varlamov.PhaseWeights7P89
