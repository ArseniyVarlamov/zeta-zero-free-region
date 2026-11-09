import PrimeNumberTheoremAnd.IEANTN.Varlamov.NonrealZeroTail

namespace Varlamov
open Real
open scoped BigOperators

lemma zero_sum_split (hK2 : KadiriExplicitInput) (j : Fin 7) {σ η τ T : ℝ}
    (hσ : (1 / 2 : ℝ) < σ) (hη : 0 < η) :
    riemannZeta.zeroes_sum (Set.Ioo 0 1) Set.univ
      (fun ρ => (F j (2 * σ - 1) η (((σ : ℂ) + (τ : ℂ) * Complex.I) - ρ)).re) =
      (1 / 2 : ℝ) * ((∑' ρ : NontrivialZeros, lowPairedTerm j σ η τ T ρ) +
        (∑' ρ : NontrivialZeros, highPairedTerm j σ η τ T ρ)) := by
  have hh0 : 0 ≤ 2 * σ - 1 := by linarith
  have hl := lowPairedTerm_summable hK2 j (τ := τ) (T := T) hσ hh0 hη
  have hr := highPairedTerm_summable hK2 j (τ := τ) (T := T) hσ hh0 hη
  have hp (ρ : NontrivialZeros) : Pi j (2 * σ - 1) η (((σ : ℂ) + (τ : ℂ) * Complex.I) - ρ) * (riemannZeta.order ρ : ℝ) =
      lowPairedTerm j σ η τ T ρ + highPairedTerm j σ η τ T ρ := by
    by_cases hc : |(ρ : ℂ).im| ≤ T
    · simp [lowPairedTerm, highPairedTerm, hc, not_lt.mpr hc]
    · simp [lowPairedTerm, highPairedTerm, hc, lt_of_not_ge hc]
  have hpair := zeroes_sum_pairing hK2 j (s := (σ : ℂ) + (τ : ℂ) * Complex.I)
    hh0 hη (by simpa using hσ) (by simp)
  rw [hpair]
  change (1 / 2 : ℝ) * (∑' ρ : NontrivialZeros,
    Pi j (2 * σ - 1) η (((σ : ℂ) + (τ : ℂ) * Complex.I) - ρ) * (riemannZeta.order ρ : ℝ)) = _
  simp_rw [hp]
  have he : (∑' ρ : NontrivialZeros, (lowPairedTerm j σ η τ T ρ + highPairedTerm j σ η τ T ρ)) =
      (∑' ρ : NontrivialZeros, lowPairedTerm j σ η τ T ρ) +
        (∑' ρ : NontrivialZeros, highPairedTerm j σ η τ T ρ) := hl.tsum_add hr
  rw [he]

lemma frequencyPoint_eq (σ t : ℝ) (k : ℕ) : frequencyPoint σ t k =
    (σ : ℂ) + ((((k : ℝ) * t : ℝ) : ℂ)) * Complex.I := by simp [frequencyPoint]

lemma nonreal_zero_sum_lower_bound (hK2 : KadiriExplicitInput) (hL1 : LehmanMonotoneInput)
    (hL2 : LehmanSquareTailInput) (hPT : PlattTrudgianInput) (j : Fin 7) {σ η t A : ℝ} {k : ℕ}
    (hA : 0 < A) (hmin : ∀ z : ℂ, Admissible z → A ≤ depth z)
    (hσdef : σ = 1 - A / Real.log (12 * t + T0)) (hσ : (1 / 2 : ℝ) < σ) (hσ1 : σ < 1)
    (hh : hMin j ≤ 2 * σ - 1) (hσeta : 1 - η ≤ σ) (hη : 0 < η) (hηmax : η ≤ etaMax j)
    (ht : H ≤ t) (hk1 : 1 ≤ k) (hk12 : k ≤ 12) (hAe : η * Real.log t = A) (hAmax : A ≤ Astar) :
    - zeroTailNonreal j ≤ riemannZeta.zeroes_sum (Set.Ioo 0 1) Set.univ
      (fun ρ => (F j (2 * σ - 1) η (frequencyPoint σ t k - ρ)).re) := by
  rw [frequencyPoint_eq, zero_sum_split hK2 j (T := 12 * t + T0) hσ hη]
  have hl : 0 ≤ ∑' ρ : NontrivialZeros, lowPairedTerm j σ η ((k : ℝ) * t) (12 * t + T0) ρ :=
    tsum_nonneg (fun ρ => lowPairedTerm_nonneg hPT j hA hmin hσdef hσ hσ1 hh hη hηmax ρ)
  have hr := nonreal_high_zero_bound hK2 hL1 hL2 j hσ hσ1 hh hσeta hη hηmax ht hk1 hk12 hAe hAmax
  linarith only [hl,hr]

lemma selected_zero_sum_lower_bound (hK2 : KadiriExplicitInput) (hL1 : LehmanMonotoneInput)
    (hL2 : LehmanSquareTailInput) (hPT : PlattTrudgianInput) (j : Fin 7) {σ η t A : ℝ}
    (hA : 0 < A) (hmin : ∀ z : ℂ, Admissible z → A ≤ depth z)
    (hσdef : σ = 1 - A / Real.log (12 * t + T0)) (hσ : (1 / 2 : ℝ) < σ) (hσ1 : σ < 1)
    (hh : hMin j ≤ 2 * σ - 1) (hσeta : 1 - η ≤ σ) (hη : 0 < η) (hηmax : η ≤ etaMax j)
    (ht : H ≤ t) (hAe : η * Real.log t = A) (hAmax : A ≤ Astar)
    (ρ₀ : NontrivialZeros) (hβ : (ρ₀ : ℂ).re = 1 - η) (hhalf : (1 / 2 : ℝ) < (ρ₀ : ℂ).re)
    (hτ : (ρ₀ : ℂ).im = t) :
    mainPairValue j σ η - zeroTailNonreal j ≤ riemannZeta.zeroes_sum (Set.Ioo 0 1) Set.univ
      (fun ρ => (F j (2 * σ - 1) η (frequencyPoint σ t 1 - ρ)).re) := by
  have hH : (0 : ℝ) < H := by norm_num [H]
  have ht0 : 0 < t := hH.trans_le ht
  have hT0 : (0 : ℝ) < T0 := by norm_num [T0]
  have hcut : |(ρ₀ : ℂ).im| ≤ 12 * t + T0 := by rw [hτ,abs_of_pos ht0]; nlinarith
  have hl := distinguished_pair_low_sum hK2 hPT j hA hmin hσdef hσ hσ1 hh hη hηmax ρ₀ hβ hhalf hτ hcut
  have hr := nonreal_high_zero_bound hK2 hL1 hL2 j (k := 1) hσ hσ1 hh hσeta hη hηmax ht (by norm_num) (by norm_num) hAe hAmax
  simp only [Nat.cast_one,one_mul] at hr
  simp only [frequencyPoint,Nat.cast_one,one_mul]
  rw [zero_sum_split hK2 j (T := 12 * t + T0) hσ hη]
  linarith only [hl,hr]

@[blueprint "varlamov-full-zero-sum-bound"
  (title := "Varlamov, Lemma 7.1: full weighted zero contribution")
  (statement := /-- At the minimal-zero parameters, every frequency has
  its required lower bound, and their nonnegative weighted sum gives
  WeightedZeroBound. The published PT, Kadiri and Lehman inputs are explicit;
  all reflection, multiplicity, selection and infinite-tail arguments are proved. -/)
  (uses := ["varlamov-real-zero-tail", "varlamov-nonreal-zero-tail",
    "varlamov-distinguished-pair", "varlamov-trigonometric-polynomial"])]
theorem weighted_zero_bound (hK2 : KadiriExplicitInput) (hL1 : LehmanMonotoneInput)
    (hL2 : LehmanSquareTailInput) (hPT : PlattTrudgianInput) (j : Fin 7) {σ η t A : ℝ}
    (hA : 0 < A) (hmin : ∀ z : ℂ, Admissible z → A ≤ depth z)
    (hσdef : σ = 1 - A / Real.log (12 * t + T0)) (hσ : (1 / 2 : ℝ) < σ) (hσ1 : σ < 1)
    (hh : hMin j ≤ 2 * σ - 1) (hσeta : 1 - η ≤ σ) (hη : 0 < η) (hηmax : η ≤ etaMax j)
    (ht : H ≤ t) (hAe : η * Real.log t = A) (hAmax : A ≤ Astar)
    (ρ₀ : NontrivialZeros) (hβ : (ρ₀ : ℂ).re = 1 - η) (hhalf : (1 / 2 : ℝ) < (ρ₀ : ℂ).re)
    (hτ : (ρ₀ : ℂ).im = t) : WeightedZeroBound j σ (2 * σ - 1) η t := by
  let V := mainPairValue j σ η
  let Z : ℕ → ℝ := fun k => riemannZeta.zeroes_sum (Set.Ioo 0 1) Set.univ
    (fun ρ => (F j (2 * σ - 1) η (frequencyPoint σ t k - ρ)).re)
  let lower : ℕ → ℝ := fun k => if k = 0 then - zeroTailReal j else
    if k = 1 then V - zeroTailNonreal j else - zeroTailNonreal j
  have hH : (0 : ℝ) < H := by norm_num [H]
  have ht0 : 0 < t := hH.trans_le ht
  have hTT0 : T0 ≤ 12 * t + T0 := by nlinarith
  have h0 : -zeroTailReal j ≤ Z 0 := by
    have h := real_zero_sum_lower_bound hK2 hL2 hPT j hA hmin hσdef hσ hσ1 hh hσeta hη hηmax hTT0
    simpa only [Z,frequencyPoint,Nat.cast_zero,zero_mul,add_zero] using h
  have h1 : V - zeroTailNonreal j ≤ Z 1 := selected_zero_sum_lower_bound hK2 hL1 hL2 hPT j hA hmin hσdef hσ hσ1 hh hσeta hη hηmax ht hAe hAmax ρ₀ hβ hhalf hτ
  have hp (k : ℕ) (hk : k ∈ Finset.range 13) : lower k ≤ Z k := by
    by_cases hk0 : k = 0
    · subst k
      simpa only [lower,ite_eq_left rfl] using h0
    · by_cases hk1 : k = 1
      · subst k
        simpa [lower] using h1
      · have hkpos : 1 ≤ k := by omega
        have hkmax : k ≤ 12 := by have := Finset.mem_range.mp hk; omega
        have h := nonreal_zero_sum_lower_bound hK2 hL1 hL2 hPT j hA hmin hσdef hσ hσ1 hh hσeta hη hηmax ht hkpos hkmax hAe hAmax
        simpa only [lower,ite_eq_right hk0,ite_eq_right hk1] using h
  have he : (∑ k ∈ Finset.range 13, Trigonometric.a k * lower k) = Trigonometric.a 1 * V - zeroTailBudget j := by
    norm_num [lower,Trigonometric.a,aPlus,Finset.sum_range_succ,zeroTailBudget]
    <;> ring
  unfold WeightedZeroBound
  change Trigonometric.a 1 * V - zeroTailBudget j ≤ ∑ k ∈ Finset.range 13, Trigonometric.a k * Z k
  rw [←he]
  apply Finset.sum_le_sum
  intro k hk
  exact mul_le_mul_of_nonneg_left (hp k hk) (Trigonometric.a_nonneg ⟨k,Finset.mem_range.mp hk⟩)

#print axioms weighted_zero_bound
end Varlamov
