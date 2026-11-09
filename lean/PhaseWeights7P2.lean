import PrimeNumberTheoremAnd.IEANTN.Varlamov.PhaseWeightBridge
import PrimeNumberTheoremAnd.IEANTN.Varlamov.PhaseCertificate7P2

namespace Varlamov.PhaseWeights7P2
open Real
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000

lemma prime_selected : 2 ∈ selectedPrimes (6 : Fin 7) := by norm_num [selectedPrimes]

lemma weight_lower_1 : (3334037860847 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (6 : Fin 7) 2 1 := by
  rw [primeOmegaWeight_piece (6 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa7, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_2 : (2002607180797 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (6 : Fin 7) 2 2 := by
  rw [primeOmegaWeight_piece (6 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa7, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_3 : (1114251204098 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (6 : Fin 7) 2 3 := by
  rw [primeOmegaWeight_piece (6 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa7, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_4 : (590842856873 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (6 : Fin 7) 2 4 := by
  rw [primeOmegaWeight_piece (6 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa7, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_5 : (304838533056 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (6 : Fin 7) 2 5 := by
  rw [primeOmegaWeight_piece (6 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa7, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_6 : (154983434740 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (6 : Fin 7) 2 6 := by
  rw [primeOmegaWeight_piece (6 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa7, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_7 : (78195307617 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (6 : Fin 7) 2 7 := by
  rw [primeOmegaWeight_piece (6 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa7, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_8 : (39298435650 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (6 : Fin 7) 2 8 := by
  rw [primeOmegaWeight_piece (6 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa7, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_9 : (19710752653 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (6 : Fin 7) 2 9 := by
  rw [primeOmegaWeight_piece (6 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa7, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_10 : (9876173619 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (6 : Fin 7) 2 10 := by
  rw [primeOmegaWeight_piece (6 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa7, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_11 : (4945908308 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (6 : Fin 7) 2 11 := by
  rw [primeOmegaWeight_piece (6 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa7, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_12 : (2476185229 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (6 : Fin 7) 2 12 := by
  rw [primeOmegaWeight_piece (6 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa7, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_13 : (1239521769 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (6 : Fin 7) 2 13 := by
  rw [primeOmegaWeight_piece (6 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa7, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_14 : (620420878 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (6 : Fin 7) 2 14 := by
  rw [primeOmegaWeight_piece (6 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa7, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_15 : (310522851 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (6 : Fin 7) 2 15 := by
  rw [primeOmegaWeight_piece (6 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa7, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_16 : (155411278 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (6 : Fin 7) 2 16 := by
  rw [primeOmegaWeight_piece (6 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa7, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_17 : (77778001 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (6 : Fin 7) 2 17 := by
  rw [primeOmegaWeight_piece (6 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa7, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_18 : (38924054 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (6 : Fin 7) 2 18 := by
  rw [primeOmegaWeight_piece (6 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa7, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_19 : (19479029 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (6 : Fin 7) 2 19 := by
  rw [primeOmegaWeight_piece (6 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa7, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

lemma weight_lower_20 : (9747762 / 10000000000000 : ℝ) ≤
    primeOmegaWeight (6 : Fin 7) 2 20 := by
  rw [primeOmegaWeight_piece (6 : Fin 7) prime_selected (by norm_num [powerCount])]
  norm_num [Multiplier.kappa, Multiplier.kappa7, hMin, sigmaMin, sigmaMax, logCutoff,
    bandHi, etaMax, Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  interval_decide (trust := kernel) <;> norm_num [div_eq_mul_inv] <;> ring

theorem phase_lower (x : ℝ) :
    (((PhaseCertificate7P2.target - 1 : ℤ) : ℝ) / PhaseSOS.targetScale) ≤ primePhase (6 : Fin 7) 2 x := by
  apply (PhaseCertificate7P2.rounded_lower_bound x).trans
  apply roundedPhase_le_primePhase (6 : Fin 7) 2 PhaseCertificate7P2.weights
    (by norm_num [PhaseCertificate7P2.weights, powerCount]) ?_ x
  intro r hr
  norm_num [PhaseCertificate7P2.weights] at hr
  interval_cases r
  · simpa [PhaseCertificate7P2.weights, PhaseSOS.weightScale] using weight_lower_1
  · simpa [PhaseCertificate7P2.weights, PhaseSOS.weightScale] using weight_lower_2
  · simpa [PhaseCertificate7P2.weights, PhaseSOS.weightScale] using weight_lower_3
  · simpa [PhaseCertificate7P2.weights, PhaseSOS.weightScale] using weight_lower_4
  · simpa [PhaseCertificate7P2.weights, PhaseSOS.weightScale] using weight_lower_5
  · simpa [PhaseCertificate7P2.weights, PhaseSOS.weightScale] using weight_lower_6
  · simpa [PhaseCertificate7P2.weights, PhaseSOS.weightScale] using weight_lower_7
  · simpa [PhaseCertificate7P2.weights, PhaseSOS.weightScale] using weight_lower_8
  · simpa [PhaseCertificate7P2.weights, PhaseSOS.weightScale] using weight_lower_9
  · simpa [PhaseCertificate7P2.weights, PhaseSOS.weightScale] using weight_lower_10
  · simpa [PhaseCertificate7P2.weights, PhaseSOS.weightScale] using weight_lower_11
  · simpa [PhaseCertificate7P2.weights, PhaseSOS.weightScale] using weight_lower_12
  · simpa [PhaseCertificate7P2.weights, PhaseSOS.weightScale] using weight_lower_13
  · simpa [PhaseCertificate7P2.weights, PhaseSOS.weightScale] using weight_lower_14
  · simpa [PhaseCertificate7P2.weights, PhaseSOS.weightScale] using weight_lower_15
  · simpa [PhaseCertificate7P2.weights, PhaseSOS.weightScale] using weight_lower_16
  · simpa [PhaseCertificate7P2.weights, PhaseSOS.weightScale] using weight_lower_17
  · simpa [PhaseCertificate7P2.weights, PhaseSOS.weightScale] using weight_lower_18
  · simpa [PhaseCertificate7P2.weights, PhaseSOS.weightScale] using weight_lower_19
  · simpa [PhaseCertificate7P2.weights, PhaseSOS.weightScale] using weight_lower_20

#print axioms phase_lower
end Varlamov.PhaseWeights7P2
