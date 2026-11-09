import PrimeNumberTheoremAnd.IEANTN.Varlamov.RemainderIdentity

namespace Varlamov.Kernel
open Real
open scoped BigOperators

/-- The constant in Lemma 4.2 decreases with its positive argument. -/
lemma C_antitoneOn : AntitoneOn C (Set.Ioi 0) := by
  intro x hx y hy hxy
  change 0 < x at hx
  change 0 < y at hy
  unfold C
  have h3 := scaled_third_pos
  have h4 := M4star_pos
  have he : exp (-y * d) ≤ exp (-x * d) := exp_le_exp.mpr (by nlinarith [d_pos])
  have hfrac : scaledDerivative 3 0 * (1 + exp (-y * d)) / y ≤
      scaledDerivative 3 0 * (1 + exp (-x * d)) / x := by
    exact div_le_div₀ (by positivity) (by gcongr) hx hxy
  have hfour : M4star / y ^ 2 ≤ M4star / x ^ 2 := by gcongr
  linarith

/-- A rational telescoping proof of the real integral-comparison bound.
The first term is retained exactly, as in Lemma 6.4. -/
lemma cubic_progression_bound {u : ℝ} (hu : 0 < u) :
    Summable (fun n : ℕ => 1 / (u + 2 * (n : ℝ)) ^ 3) ∧
      (∑' n : ℕ, 1 / (u + 2 * (n : ℝ)) ^ 3) ≤ 1 / u ^ 3 + 1 / (4 * u ^ 2) := by
  have hstep (x : ℝ) (hx : 0 < x) :
      1 / (x + 2) ^ 3 ≤ 1 / (4 * x ^ 2) - 1 / (4 * (x + 2) ^ 2) := by
    have hx2 : 0 < x + 2 := by linarith
    apply (le_sub_iff_add_le).mpr
    field_simp
    nlinarith [sq_nonneg x]
  have htel (N : ℕ) :
      (∑ n ∈ Finset.range N, 1 / (u + 2 * ((n + 1 : ℕ) : ℝ)) ^ 3) ≤
        1 / (4 * u ^ 2) - 1 / (4 * (u + 2 * (N : ℝ)) ^ 2) := by
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ]
      have h := hstep (u + 2 * (N : ℝ)) (by positivity)
      simp only [Nat.cast_add, Nat.cast_one] at h ih ⊢
      have he : u + 2 * ((N : ℝ) + 1) = (u + 2 * (N : ℝ)) + 2 := by ring
      rw [he]
      linarith
  have hb (N : ℕ) : (∑ n ∈ Finset.range N, 1 / (u + 2 * (n : ℝ)) ^ 3) ≤
      1 / u ^ 3 + 1 / (4 * u ^ 2) := by
    cases N with
    | zero => simp only [Finset.sum_range_zero]; positivity
    | succ N =>
      rw [Finset.sum_range_succ']
      have h := htel N
      have hn : 0 ≤ 1 / (4 * (u + 2 * (N : ℝ)) ^ 2) := by positivity
      simp only [Nat.cast_zero, mul_zero, add_zero]
      linarith
  have hnonneg (n : ℕ) : 0 ≤ 1 / (u + 2 * (n : ℝ)) ^ 3 := by positivity
  exact ⟨summable_of_sum_range_le hnonneg hb,
    Real.tsum_le_of_sum_range_le hnonneg hb⟩

/-- The transform bound at every sample, with an independently specified
lower bound for its real part and upper bound for eta. -/
lemma zeroSample_succ_bound {η ηmax u : ℝ} {s : ℂ}
    (hη : 0 < η) (hηmax : η ≤ ηmax) (hu : 0 < u) (hsu : u ≤ s.re + 2) (n : ℕ) :
    ‖zeroSample η s (n + 1)‖ ≤ C (u / ηmax) * η ^ 3 / ‖s + 2 * ((n + 1 : ℕ) : ℂ)‖ ^ 3 := by
  have hηm : 0 < ηmax := hη.trans_le hηmax
  have hre : u ≤ (s + 2 * ((n + 1 : ℕ) : ℂ)).re := by
    simp
    
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hb := W0_scaled_norm hη hu hre
  have hc : C (u / η) ≤ C (u / ηmax) := C_antitoneOn
    (div_pos hu hηm) (div_pos hu hη) (by gcongr)
  exact hb.trans (by gcongr)

/-- The real-axis part of Lemma 6.4, with the exact constant in the article. -/
theorem Delta_real_bound (hC : HalfPlaneCauchyInput) {η ηmax u : ℝ} {s : ℂ}
    (hη : 0 < η) (hηmax : η ≤ ηmax) (hs : (1 / 2 : ℝ) < s.re)
    (hu : 0 < u) (hsu : u ≤ s.re + 2) :
    ‖Delta η s‖ ≤ C (u / ηmax) * η ^ 3 * (1 / u ^ 3 + 1 / (4 * u ^ 2)) := by
  let P := C (u / ηmax) * η ^ 3
  have hP : 0 ≤ P := by dsimp [P]; exact mul_nonneg (C_pos (div_pos hu (hη.trans_le hηmax))).le (by positivity)
  have hb (n : ℕ) : ‖zeroSample η s (n + 1)‖ ≤ P * (1 / (u + 2 * (n : ℝ)) ^ 3) := by
    have hre : u + 2 * (n : ℝ) ≤ (s + 2 * ((n + 1 : ℕ) : ℂ)).re := by
      simp
      
      linarith
    have hn := hre.trans (Complex.re_le_norm (s + 2 * ((n + 1 : ℕ) : ℂ)))
    calc
      _ ≤ P / ‖s + 2 * ((n + 1 : ℕ) : ℂ)‖ ^ 3 := zeroSample_succ_bound hη hηmax hu hsu n
      _ ≤ P / (u + 2 * (n : ℝ)) ^ 3 := by gcongr
      _ = _ := by ring
  have hsum := cubic_progression_bound hu
  have hnorm := (Delta_trivial_zeros hC hη hs).1
  rw [(Delta_trivial_zeros hC hη hs).2, norm_neg]
  calc
    _ ≤ ∑' n : ℕ, ‖zeroSample η s (n + 1)‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' n : ℕ, P * (1 / (u + 2 * (n : ℝ)) ^ 3) := hnorm.tsum_le_tsum hb (hsum.1.mul_left P)
    _ = P * (∑' n : ℕ, 1 / (u + 2 * (n : ℝ)) ^ 3) := tsum_mul_left
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum.2 hP

#print axioms Delta_real_bound
end Varlamov.Kernel
