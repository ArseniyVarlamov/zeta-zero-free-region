import PrimeNumberTheoremAnd.IEANTN.Varlamov.TestFunction
import PrimeNumberTheoremAnd.IEANTN.Varlamov.Trigonometric
import PrimeNumberTheoremAnd.IEANTN.Varlamov.PairChecks
import Mathlib.Data.Nat.Prime.Int

namespace Varlamov
open Real
open scoped BigOperators

noncomputable def selectedPrimes (j : Fin 7) : Finset ℕ :=
  if j.val = 6 then {2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97}
  else {2,3,5,7,11,13,17,19}
def powerCount (j : Fin 7) : ℕ := if j.val = 6 then 20 else 10
noncomputable def primePowerPairs (j : Fin 7) : Finset (ℕ × ℕ) :=
  (selectedPrimes j).product (Finset.Icc 1 (powerCount j))

lemma selected_primes_valid (j : Fin 7) : ∀ p ∈ selectedPrimes j, p.Prime ∧ p ≤ 97 := by
  fin_cases j <;> norm_num [selectedPrimes] <;> decide +kernel
lemma powerCount_pos (j : Fin 7) : 0 < powerCount j := by unfold powerCount; split_ifs <;> norm_num
lemma scale_powerCount_bound (j : Fin 7) : etaMax j * (powerCount j : ℝ) < (1 / 10 : ℝ) := by
  fin_cases j <;> norm_num [etaMax, powerCount]

/-- The actual retained integers are distinct, with both the prime and
exponent recovered from a prime power equality. -/
theorem selected_prime_powers_injective (j : Fin 7) :
    Set.InjOn (fun pr : ℕ × ℕ => pr.1 ^ pr.2) (primePowerPairs j : Set (ℕ × ℕ)) := by
  intro x hx y hy he
  have hx' := Finset.mem_product.mp hx
  have hy' := Finset.mem_product.mp hy
  have hp := (selected_primes_valid j x.1 hx'.1).1
  have hq := (selected_primes_valid j y.1 hy'.1).1
  have hr : x.2 ≠ 0 := by have := (Finset.mem_Icc.mp hx'.2).1; omega
  have hs : y.2 ≠ 0 := by have := (Finset.mem_Icc.mp hy'.2).1; omega
  obtain ⟨hxy, hrs⟩ := hp.pow_inj' hq hr hs he
  exact Prod.ext hxy hrs

lemma w_half_pos : 0 < Kernel.w (1 / 2 : ℝ) := by
  rw [Kernel.w_piece ⟨by norm_num, by norm_num [Kernel.d]⟩]
  norm_num [Kernel.piece, Kernel.unit, Kernel.unitPoly, Kernel.d]
lemma w_pos_of_le_half {u : ℝ} (hu : 0 ≤ u) (huh : u ≤ 1 / 2) : 0 < Kernel.w u :=
  w_half_pos.trans_le (Kernel.w_antitone hu (by norm_num) huh)

lemma prime_kernel_argument (j : Fin 7) {p r : ℕ} (hp : p ∈ selectedPrimes j)
    (hr : r ∈ Finset.Icc 1 (powerCount j)) :
    0 < etaMax j * (r : ℝ) * Real.log p ∧ etaMax j * (r : ℝ) * Real.log p < 1 / 2 := by
  have hp' := selected_primes_valid j p hp
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp'.1.two_le
  have hp97 : (p : ℝ) ≤ 97 := by exact_mod_cast hp'.2
  have hl : 0 < Real.log p := Real.log_pos (by linarith)
  have hl5 : Real.log p < 5 := by
    apply lt_of_le_of_lt (Real.log_le_log (by linarith : (0 : ℝ) < p) hp97)
    interval_decide (trust := kernel)
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast (Finset.mem_Icc.mp hr).1
  have hrmax : (r : ℝ) ≤ powerCount j := by exact_mod_cast (Finset.mem_Icc.mp hr).2
  have hη := (etaMax_range j).1
  have hb := scale_powerCount_bound j
  constructor
  · positivity
  · have hscale : etaMax j * (r : ℝ) < 1 / 10 :=
      (mul_le_mul_of_nonneg_left hrmax hη.le).trans_lt hb
    nlinarith

noncomputable def primeOmegaWeight (j : Fin 7) (p r : ℕ) : ℝ :=
  Multiplier.kappa j (Real.exp (-hMin j * (r : ℝ) * Real.log p)) *
    (Kernel.w (etaMax j * (r : ℝ) * Real.log p) / 10) *
    Real.exp (-sigmaMax j * (r : ℝ) * Real.log p)
/-- Equality to the real-power weights printed in the manuscript. -/
lemma primeOmegaWeight_eq_rpow (j : Fin 7) {p : ℕ} (hp : p ∈ selectedPrimes j) (r : ℕ) :
    primeOmegaWeight j p r = Multiplier.kappa j ((p : ℝ) ^ (-(r : ℝ) * hMin j)) *
      (Kernel.w (etaMax j * (r : ℝ) * Real.log p) / 10) * ((p : ℝ) ^ (-(r : ℝ) * sigmaMax j)) := by
  have hp0 : (0 : ℝ) < p := by
    have := (selected_primes_valid j p hp).1.two_le
    exact_mod_cast (show 0 < p by omega)
  rw [Real.rpow_def_of_pos hp0, Real.rpow_def_of_pos hp0]
  have he1 : Real.log p * (-(r : ℝ) * hMin j) = -hMin j * (r : ℝ) * Real.log p := by ring
  have he2 : Real.log p * (-(r : ℝ) * sigmaMax j) = -sigmaMax j * (r : ℝ) * Real.log p := by ring
  rw [he1, he2]
  rfl

noncomputable def primePhase (j : Fin 7) (p : ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (powerCount j), primeOmegaWeight j p (n + 1) * Trigonometric.P (((n + 1 : ℕ) : ℝ) * x)
noncomputable def phaseCosineCoefficient (j : Fin 7) (p l : ℕ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 (powerCount j), ∑ k ∈ Finset.range 13,
    if r * k = l then primeOmegaWeight j p r * Trigonometric.a k else 0

@[blueprint "varlamov-prime-weights"
  (title := "Varlamov, C12: prime-power weights")
  (statement := /-- The selected integers are genuine distinct prime powers,
  and their actual kernel and multiplier weights are positive. This does
  not certify the phase minima or the prime-sum lower bound of Lemma 7.4. -/)
  (uses := ["varlamov-kernel-autocorrelation", "varlamov-trigonometric-polynomial"])]
theorem primeOmegaWeight_pos (j : Fin 7) {p r : ℕ} (hp : p ∈ selectedPrimes j)
    (hr : r ∈ Finset.Icc 1 (powerCount j)) : 0 < primeOmegaWeight j p r := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (selected_primes_valid j p hp).1.two_le
  have hl : 0 < Real.log p := Real.log_pos (by linarith)
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast (Finset.mem_Icc.mp hr).1
  have hh := hMin_pos j
  have he : Real.exp (-hMin j * (r : ℝ) * Real.log p) ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr ?_⟩
    nlinarith [mul_nonneg (mul_nonneg hh.le (show (0 : ℝ) ≤ r by linarith)) hl.le]
  have hk := Multiplier.kappa_pos j he
  have hu := prime_kernel_argument j hp hr
  have hw := w_pos_of_le_half hu.1.le hu.2.le
  unfold primeOmegaWeight
  positivity

theorem primePhase_nonneg (j : Fin 7) {p : ℕ} (hp : p ∈ selectedPrimes j) (x : ℝ) : 0 ≤ primePhase j p x := by
  unfold primePhase
  apply Finset.sum_nonneg
  intro n hn
  have hr : n + 1 ∈ Finset.Icc 1 (powerCount j) := by simp only [Finset.mem_Icc]; have := Finset.mem_range.mp hn; omega
  exact mul_nonneg (primeOmegaWeight_pos j hp hr).le (Trigonometric.P_nonneg _)

theorem phase_cosine_coefficients_nonneg (j : Fin 7) {p : ℕ} (hp : p ∈ selectedPrimes j) (l : ℕ) :
    0 ≤ phaseCosineCoefficient j p l := by
  unfold phaseCosineCoefficient
  apply Finset.sum_nonneg
  intro r hr
  apply Finset.sum_nonneg
  intro k hk
  split_ifs
  · exact mul_nonneg (primeOmegaWeight_pos j hp hr).le (Trigonometric.a_nonneg ⟨k, Finset.mem_range.mp hk⟩)
  · exact le_rfl

#print axioms selected_prime_powers_injective
#print axioms primeOmegaWeight_pos
#print axioms phase_cosine_coefficients_nonneg
end Varlamov
