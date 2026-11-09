import PrimeNumberTheoremAnd.IEANTN.Varlamov.PrimeData
import Mathlib.Algebra.BigOperators.Intervals

namespace Varlamov
open Real
open scoped BigOperators

/-- This is the remaining C12 certificate obligation, not a literature input
and not a proved fact about the manuscript's positive J_p values. -/
def PrimePhaseCertificate (j : Fin 7) (Jp : ℕ → ℝ) : Prop :=
  ∀ p ∈ selectedPrimes j, ∀ x : ℝ, Jp p ≤ primePhase j p x
noncomputable def primeLowerBudget (j : Fin 7) (Jp : ℕ → ℝ) : ℝ :=
  ∑ p ∈ selectedPrimes j, Jp p * Real.log p
noncomputable def primeContribution (j : Fin 7) (σ h η t : ℝ) (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n * Real.exp (-σ * Real.log n) *
    testFunction j h η (Real.log n) * Trigonometric.P (t * Real.log n)

lemma primeContribution_eq_rpow (j : Fin 7) (σ h η t : ℝ) (n : ℕ) :
    primeContribution j σ h η t n = ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-σ) *
      testFunction j h η (Real.log n) * Trigonometric.P (t * Real.log n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [primeContribution]
  · rw [Real.rpow_def_of_pos (Nat.cast_pos.mpr hn),
      show Real.log n * (-σ) = -σ * Real.log n from by ring]
    rfl

lemma testFunction_zero_after (j : Fin 7) {η : ℝ} (hη : 0 < η) (h : ℝ)
    {u : ℝ} (hu : Kernel.d / η < u) : testFunction j h η u = 0 := by
  have he : Kernel.smoothKernel η u = 0 := Kernel.smoothDerivative_zero_of_gt 0 hη hu
  simp only [testFunction, he, zero_mul]

lemma testFunction_nonneg (j : Fin 7) {η h u : ℝ} (hη : 0 < η) (hh : 0 ≤ h) (hu : 0 ≤ u) :
    0 ≤ testFunction j h η u := by
  have he : Real.exp (-h * u) ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr ?_⟩
    nlinarith
  rw [testFunction_eq_article j hη h hu]
  exact mul_nonneg (Kernel.g_nonneg hη.le u) (Multiplier.kappa_pos j he).le

lemma primeContribution_nonneg (j : Fin 7) {η h σ t : ℝ} (hη : 0 < η) (hh : 0 ≤ h) (n : ℕ) :
    0 ≤ primeContribution j σ h η t n := by
  have hlog : 0 ≤ Real.log n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · exact Real.log_nonneg (by exact_mod_cast hn)
  exact mul_nonneg (mul_nonneg (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
    (Real.exp_pos _).le) (testFunction_nonneg j hη hh hlog)) (Trigonometric.P_nonneg _)

lemma primeContribution_summable (j : Fin 7) {η : ℝ} (hη : 0 < η) (σ h t : ℝ) :
    Summable (primeContribution j σ h η t) := by
  apply summable_of_hasFiniteSupport
  apply Set.Finite.subset (Set.finite_Iic ⌊Real.exp (Kernel.d / η)⌋₊)
  intro n hn
  have hf : testFunction j h η (Real.log n) ≠ 0 := by
    intro hf
    exact hn (by simp [primeContribution, hf])
  have hl : Real.log n ≤ Kernel.d / η := by
    by_contra hcontra
    exact hf (testFunction_zero_after j hη h (lt_of_not_ge hcontra))
  rw [Set.mem_Iic]
  apply Nat.le_floor
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · exact_mod_cast (Real.exp_pos (Kernel.d / η)).le
  · rw [← Real.exp_log (Nat.cast_pos.mpr hn0), Real.exp_le_exp]
    exact hl

lemma phase_Icc (j : Fin 7) (p : ℕ) (x : ℝ) : primePhase j p x =
    ∑ r ∈ Finset.Icc 1 (powerCount j), primeOmegaWeight j p r * Trigonometric.P ((r : ℝ) * x) := by
  have he : Finset.Icc 1 (powerCount j) = Finset.Ico 1 (powerCount j + 1) := by
    ext r
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [he, Finset.sum_Ico_eq_sum_range]
  simpa only [primePhase, Nat.add_sub_cancel, Nat.add_comm 1]

lemma sample_weight_lower (j : Fin 7) {η h σ u : ℝ}
    (hη : 0 < η) (hηmax : η ≤ etaMax j) (hh : hMin j ≤ h) (hσ : σ ≤ sigmaMax j)
    (hu : 0 ≤ u) :
    η * (Real.exp (-sigmaMax j * u) * Kernel.w (etaMax j * u) *
      Multiplier.kappa j (Real.exp (-hMin j * u))) ≤
      Real.exp (-σ * u) * testFunction j h η u := by
  have hh0 : 0 ≤ h := (hMin_pos j).le.trans hh
  have hhm := (hMin_pos j).le
  have heh : Real.exp (-h * u) ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr ?_⟩
    nlinarith
  have hem : Real.exp (-hMin j * u) ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr ?_⟩
    nlinarith
  have hb : Real.exp (-h * u) ≤ Real.exp (-hMin j * u) := Real.exp_le_exp.mpr (by nlinarith)
  have hk := (Multiplier.kappa_strictAnti j).antitoneOn heh hem hb
  have hw := Kernel.w_antitone (mul_nonneg hη.le hu)
    (mul_nonneg (etaMax_range j).1.le hu) (mul_le_mul_of_nonneg_right hηmax hu)
  have hs : Real.exp (-sigmaMax j * u) ≤ Real.exp (-σ * u) := Real.exp_le_exp.mpr (by nlinarith)
  have hk0 := (Multiplier.kappa_pos j hem).le
  have hkh0 := (Multiplier.kappa_pos j heh).le
  have hw0 := Kernel.w_nonneg (etaMax j * u)
  have hwh0 := Kernel.w_nonneg (η * u)
  rw [testFunction_eq_article j hη h hu]
  simp only [Kernel.g, ite_eq_left hu]
  calc
    _ ≤ η * (Real.exp (-σ * u) * Kernel.w (η * u) * Multiplier.kappa j (Real.exp (-h * u))) := by gcongr
    _ = _ := by ring

lemma retained_prime_bound (j : Fin 7) {η h σ t : ℝ}
    (hη : 0 < η) (hηmax : η ≤ etaMax j) (hh : hMin j ≤ h) (hσ : σ ≤ sigmaMax j)
    {p r : ℕ} (hp : p ∈ selectedPrimes j) (hr : r ∈ Finset.Icc 1 (powerCount j)) :
    η * 10 * Real.log p * (primeOmegaWeight j p r * Trigonometric.P ((r : ℝ) * (t * Real.log p))) ≤
      primeContribution j σ h η t (p ^ r) := by
  have hpP := (selected_primes_valid j p hp).1
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpP.two_le
  have hlog : 0 < Real.log p := Real.log_pos (by linarith)
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast (Finset.mem_Icc.mp hr).1
  have hr0 : r ≠ 0 := by have := (Finset.mem_Icc.mp hr).1; omega
  have he : Real.log ((p ^ r : ℕ) : ℝ) = (r : ℝ) * Real.log p := by rw [Nat.cast_pow, Real.log_pow]
  have hbase := sample_weight_lower j hη hηmax hh hσ (show 0 ≤ (r : ℝ) * Real.log p by positivity)
  unfold primeContribution
  rw [ArithmeticFunction.vonMangoldt_apply_pow hr0, ArithmeticFunction.vonMangoldt_apply_prime hpP, he]
  have hP : 0 ≤ Trigonometric.P ((r : ℝ) * (t * Real.log p)) := Trigonometric.P_nonneg _
  have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbase hlog.le) hP
  have harg : t * ((r : ℝ) * Real.log p) = (r : ℝ) * (t * Real.log p) := by ring
  rw [harg]
  convert h using 1 <;> (try dsimp only [primeOmegaWeight]) <;> ring

@[blueprint "varlamov-prime-lifting"
  (title := "Varlamov, Lemma 7.4: lifting certified phase bounds")
  (statement := /-- Given the explicitly stated finite phase-certificate
  obligation C12, the full sum over prime powers is at least $\eta w_0J$.
  The positive numerical J_p values themselves remain uncertified here;
  this theorem does not declare them to be external literature inputs. -/)
  (uses := ["varlamov-prime-weights", "varlamov-trigonometric-polynomial"])]
theorem prime_powers_lower_bound (j : Fin 7) (Jp : ℕ → ℝ)
    (hJ : PrimePhaseCertificate j Jp) {η h σ t : ℝ}
    (hη : 0 < η) (hηmax : η ≤ etaMax j) (hh : hMin j ≤ h) (hσ : σ ≤ sigmaMax j) :
    η * 10 * primeLowerBudget j Jp ≤ ∑' n : ℕ, primeContribution j σ h η t n := by
  have hh0 : 0 ≤ h := (hMin_pos j).le.trans hh
  have hs := primeContribution_summable j hη σ h t
  let nums := (primePowerPairs j).image (fun pr : ℕ × ℕ => pr.1 ^ pr.2)
  have hretained : (∑ pr ∈ primePowerPairs j, primeContribution j σ h η t (pr.1 ^ pr.2)) ≤
      ∑' n : ℕ, primeContribution j σ h η t n := by
    have he : (∑ pr ∈ primePowerPairs j, primeContribution j σ h η t (pr.1 ^ pr.2)) =
        ∑ n ∈ nums, primeContribution j σ h η t n := by
      dsimp [nums]
      rw [Finset.sum_image]
      intro x hx y hy he
      exact selected_prime_powers_injective j hx hy he
    rw [he]
    exact Summable.sum_le_tsum _ (fun n _ => primeContribution_nonneg j hη hh0 n) hs
  apply le_trans ?_ hretained
  unfold primePowerPairs
  rw [show (selectedPrimes j).product (Finset.Icc 1 (powerCount j)) =
    (selectedPrimes j) ×ˢ (Finset.Icc 1 (powerCount j)) from rfl, Finset.sum_product]
  unfold primeLowerBudget
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (selected_primes_valid j p hp).1.two_le
  have hlog : 0 < Real.log p := Real.log_pos (by linarith)
  calc
    η * 10 * (Jp p * Real.log p) ≤ η * 10 * Real.log p * primePhase j p (t * Real.log p) := by
      have h := mul_le_mul_of_nonneg_left (hJ p hp (t * Real.log p)) (show 0 ≤ η * 10 * Real.log p by positivity)
      convert h using 1 <;> ring
    _ = ∑ r ∈ Finset.Icc 1 (powerCount j), η * 10 * Real.log p *
        (primeOmegaWeight j p r * Trigonometric.P ((r : ℝ) * (t * Real.log p))) := by
      rw [phase_Icc, Finset.mul_sum]
    _ ≤ _ := Finset.sum_le_sum (fun r hr => retained_prime_bound j hη hηmax hh hσ hp hr)

/-- The actual infimum, used without assuming any numerical phase certificate. -/
noncomputable def primePhaseInf (j : Fin 7) (p : ℕ) : ℝ := sInf (Set.range (primePhase j p))

lemma primePhaseInf_certificate (j : Fin 7) : PrimePhaseCertificate j (primePhaseInf j) := by
  intro p hp x
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro y ⟨u, rfl⟩
    exact primePhase_nonneg j hp u
  · exact Set.mem_range_self x

lemma primePhaseInf_nonneg (j : Fin 7) {p : ℕ} (hp : p ∈ selectedPrimes j) : 0 ≤ primePhaseInf j p := by
  apply le_csInf (Set.range_nonempty _)
  rintro y ⟨u, rfl⟩
  exact primePhase_nonneg j hp u

lemma phase_certificate_le_inf (j : Fin 7) (Jp : ℕ → ℝ) (hJ : PrimePhaseCertificate j Jp)
    {p : ℕ} (hp : p ∈ selectedPrimes j) : Jp p ≤ primePhaseInf j p := by
  apply le_csInf (Set.range_nonempty _)
  rintro y ⟨x, rfl⟩
  exact hJ p hp x

lemma prime_budget_le_inf (j : Fin 7) (Jp : ℕ → ℝ) (hJ : PrimePhaseCertificate j Jp) :
    primeLowerBudget j Jp ≤ primeLowerBudget j (primePhaseInf j) := by
  apply Finset.sum_le_sum
  intro p hp
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (selected_primes_valid j p hp).1.two_le
  exact mul_le_mul_of_nonneg_right (phase_certificate_le_inf j Jp hJ hp)
    (Real.log_nonneg (by linarith))

/-- The analytic prime-power lower bound is unconditional if J is defined
by the true infima. The numerical lower enclosures of those infima are still
an outstanding finite certificate. -/
theorem prime_powers_inf_lower_bound (j : Fin 7) {η h σ t : ℝ}
    (hη : 0 < η) (hηmax : η ≤ etaMax j) (hh : hMin j ≤ h) (hσ : σ ≤ sigmaMax j) :
    η * 10 * primeLowerBudget j (primePhaseInf j) ≤ ∑' n : ℕ, primeContribution j σ h η t n :=
  prime_powers_lower_bound j (primePhaseInf j) (primePhaseInf_certificate j) hη hηmax hh hσ

#print axioms prime_powers_inf_lower_bound
#print axioms prime_powers_lower_bound
end Varlamov
