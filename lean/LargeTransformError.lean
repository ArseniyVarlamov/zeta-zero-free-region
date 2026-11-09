import PrimeNumberTheoremAnd.IEANTN.Varlamov.MarginWBridge

namespace Varlamov
open Real
open scoped BigOperators

lemma coefficient_abs_le_one (j : Fin 7) {m : ℕ} (hm : m < Multiplier.length j) :
    |Multiplier.coefficient j m| ≤ 1 := by
  fin_cases j <;> norm_num [Multiplier.length] at hm
  all_goals interval_cases m <;> norm_num [Multiplier.coefficient,
    Multiplier.coefficient1, Multiplier.coefficient2, Multiplier.coefficient3,
    Multiplier.coefficient4, Multiplier.coefficient5, Multiplier.coefficient6, Multiplier.coefficient7]

noncomputable def largeTerms (j : Fin 7) (W : ℝ → ℝ) (μ η : ℝ) : ℝ :=
  Trigonometric.a 1 * (∑ m ∈ Finset.range (Multiplier.length j),
    Multiplier.coefficient j m * W (argumentOne μ η m)) +
  (∑ n ∈ Finset.range (Multiplier.length j - 1), Multiplier.coefficient j (n + 1) *
    (Trigonometric.a 1 * W (argumentTwo μ η (n + 1)) - W (argumentThree μ η (n + 1))))

lemma abs_sum_sub_le {n : ℕ} {f g : ℕ → ℝ} {ε : ℝ}
    (h : ∀ i < n, |f i - g i| ≤ ε) :
    |(∑ i ∈ Finset.range n, f i) - ∑ i ∈ Finset.range n, g i| ≤ n * ε := by
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _i ∈ Finset.range n, ε := Finset.sum_le_sum (fun i hi => h i (Finset.mem_range.mp hi))
    _ = _ := by simp

lemma scalar_error {c a b : ℝ} (hc : |c| ≤ 1) (he : |a - b| ≤ (1e-20 : ℝ)) :
    |c * a - c * b| ≤ (1e-20 : ℝ) := by
  rw [← mul_sub, abs_mul]
  have h := mul_le_mul hc he (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  simpa using h

lemma three_scalar_error {c a b u v : ℝ} (hc : |c| ≤ 1)
    (h1 : |a - u| ≤ (1e-20 : ℝ)) (h2 : |b - v| ≤ (1e-20 : ℝ)) :
    |c * (Trigonometric.a 1 * a - b) - c * (Trigonometric.a 1 * u - v)| ≤ (3e-20 : ℝ) := by
  have ha : |Trigonometric.a 1| ≤ (2 : ℝ) := by norm_num [Trigonometric.a]
  have he : c * (Trigonometric.a 1 * a - b) - c * (Trigonometric.a 1 * u - v) =
      c * (Trigonometric.a 1 * (a - u) - (b - v)) := by ring
  rw [he, abs_mul]
  have hab : |Trigonometric.a 1 * (a - u) - (b - v)| ≤ (3e-20 : ℝ) := by
    apply (abs_sub _ _).trans
    rw [abs_mul]
    have hp := mul_le_mul ha h1 (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
    linarith only [hp, h2]
  have hp := mul_le_mul hc hab (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  simpa using hp

/-- Uniform error for every large W term of the actual margin. The harmless
padding is much larger than the certified omitted exponential endpoints. -/
theorem largeTerms_rational_error (j : Fin 7) {μ η : ℝ}
    (hμ : μ < 1) (hη : 0 < η) (hηmax : η < etaMax j) :
    |largeTerms j realW μ η - largeTerms j rationalW μ η| ≤ (1e-17 : ℝ) := by
  obtain ⟨h1,h23,_⟩ := large_arguments_bound j hμ hη hηmax
  have hν : (130 : ℝ) ≤ 1 / etaMax j - 3 := by fin_cases j <;> norm_num [etaMax]
  have hW1 (m : ℕ) := realW_rational_error (hν.trans (h1 m).le)
  have hW2 (m : ℕ) (hm : 1 ≤ m) := realW_rational_error (hν.trans (h23 m hm).1.le)
  have hW3 (m : ℕ) (hm : 1 ≤ m) := realW_rational_error (hν.trans (h23 m hm).2.le)
  have hfirst := abs_sum_sub_le (n := Multiplier.length j)
    (fun m hm => scalar_error (coefficient_abs_le_one j hm) (hW1 m))
  have hsecond := abs_sum_sub_le (n := Multiplier.length j - 1)
    (fun n hn => three_scalar_error
      (coefficient_abs_le_one j (show n + 1 < Multiplier.length j by omega))
      (hW2 (n + 1) (by omega)) (hW3 (n + 1) (by omega)))
  have hn : (Multiplier.length j : ℝ) ≤ 15 := by exact_mod_cast degree_upper j
  have hn' : ((Multiplier.length j - 1 : ℕ) : ℝ) ≤ 15 := by
    exact_mod_cast (show Multiplier.length j - 1 ≤ 15 by have := degree_upper j; omega)
  have ha : |Trigonometric.a 1| ≤ (2 : ℝ) := by norm_num [Trigonometric.a]
  rw [show largeTerms j realW μ η - largeTerms j rationalW μ η = Trigonometric.a 1 *
      ((∑ m ∈ Finset.range (Multiplier.length j), Multiplier.coefficient j m * realW (argumentOne μ η m)) -
       ∑ m ∈ Finset.range (Multiplier.length j), Multiplier.coefficient j m * rationalW (argumentOne μ η m)) +
      ((∑ n ∈ Finset.range (Multiplier.length j - 1), Multiplier.coefficient j (n + 1) *
        (Trigonometric.a 1 * realW (argumentTwo μ η (n + 1)) - realW (argumentThree μ η (n + 1)))) -
       ∑ n ∈ Finset.range (Multiplier.length j - 1), Multiplier.coefficient j (n + 1) *
        (Trigonometric.a 1 * rationalW (argumentTwo μ η (n + 1)) - rationalW (argumentThree μ η (n + 1)))) from by unfold largeTerms; ring]
  apply (abs_add_le _ _).trans
  rw [abs_mul]
  have hp := mul_le_mul ha hfirst (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
  nlinarith only [hp, hsecond, hn, hn']

#print axioms largeTerms_rational_error
end Varlamov
