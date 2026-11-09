import PrimeNumberTheoremAnd.IEANTN.Varlamov.MarginExpressionSemantics
import PrimeNumberTheoremAnd.IEANTN.Varlamov.MomentCertificates

namespace Varlamov.MarginExpression
open Real
open scoped BigOperators

lemma horner_eq_sum (cs : List ℚ) (x : ℝ) :
    horner cs x = ∑ n ∈ Finset.range cs.length, ((cs.getD n 0 : ℚ) : ℝ) * x ^ n := by
  induction cs with
  | nil => simp [horner]
  | cons c cs ih =>
    change (c : ℝ) + x * horner cs x = _
    simp only [List.length_cons]
    rw [Finset.sum_range_succ']
    simp only [List.getD_cons_zero, List.getD_cons_succ, pow_zero, mul_one]
    rw [ih, Finset.mul_sum, add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro n _
    rw [pow_succ]
    ring

lemma moment_coefficient_lower (n : Fin 9) :
    (-1 : ℝ) ^ (n : ℕ) * ((moments.getD n 0 : ℚ) : ℝ) ≤
      (-1 : ℝ) ^ (n : ℕ) * moment n / ((n : ℕ).factorial : ℝ) := by
  obtain ⟨hl,hu⟩ := moment_bounds n
  fin_cases n <;> norm_num [moments, momentLower, momentUpper, Nat.factorial] at * <;> linarith

/-- The polynomial used by C13 is a proved lower enclosure of the actual
Taylor sum of the nine integral moments. -/
theorem horner_moments_le_taylor {μ : ℝ} (hμ : μ ≤ 1) :
    horner moments (μ - 1) ≤ taylorSum μ := by
  rw [horner_eq_sum]
  have hlen : moments.length = 9 := rfl
  rw [hlen]
  unfold taylorSum
  apply Finset.sum_le_sum
  intro n hn
  have hn' : n < 9 := Finset.mem_range.mp hn
  have hc := moment_coefficient_lower ⟨n,hn'⟩
  have hv : 0 ≤ (1 - μ) ^ n := pow_nonneg (by linarith) n
  have hm := mul_le_mul_of_nonneg_right hc hv
  have he : μ - 1 = (-1 : ℝ) * (1 - μ) := by ring
  rw [he, mul_pow]
  convert hm using 1 <;> ring

#print axioms horner_moments_le_taylor
end Varlamov.MarginExpression
