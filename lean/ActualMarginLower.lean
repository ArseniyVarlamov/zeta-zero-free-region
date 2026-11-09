import PrimeNumberTheoremAnd.IEANTN.Varlamov.MomentLowerPolynomial
import PrimeNumberTheoremAnd.IEANTN.Varlamov.LargeTransformError
import PrimeNumberTheoremAnd.IEANTN.Varlamov.MarginScalars

namespace Varlamov.MarginExpression
open Real
open scoped BigOperators

lemma value_as_lower (j : Fin 7) {μ η A : ℝ} (hη : η ≠ 0) :
    value j μ η A = horner moments (μ - 1) + largeTerms j Varlamov.rationalW μ η +
      (10 * (((data j).gamma : ℝ) + ((data j).prime : ℝ)) - 1e-10) * η -
      (13 * η ^ 3 + (1e-7 : ℝ) + 1e-12 + 1e-17 + ((data j).q : ℝ) * A) := by
  have h1 : (∑ m ∈ Finset.range (data j).coeffs.length,
      ((a1 * (data j).coeffs.getD m 0 : ℚ) : ℝ) * realWInv (inverseOneReal μ η m)) =
      Trigonometric.a 1 * (∑ m ∈ Finset.range (Multiplier.length j),
        Multiplier.coefficient j m * Varlamov.rationalW (argumentOne μ η m)) := by
    rw [margin_coeffs_length, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    rw [Rat.cast_mul, margin_coefficients j (Finset.mem_range.mp hm), a1_eq,
      inverseOne_eq hη, realWInv_eq_rationalW]
    ring
  have h2 : (∑ n ∈ Finset.range ((data j).coeffs.length - 1),
      (((data j).coeffs.getD (n + 1) 0 : ℚ) : ℝ) *
        ((a1 : ℝ) * realWInv (inverseTwoReal μ η (n + 1)) - realWInv (inverseThreeReal μ η (n + 1)))) =
      ∑ n ∈ Finset.range (Multiplier.length j - 1), Multiplier.coefficient j (n + 1) *
        (Trigonometric.a 1 * Varlamov.rationalW (argumentTwo μ η (n + 1)) -
          Varlamov.rationalW (argumentThree μ η (n + 1))) := by
    rw [margin_coeffs_length]
    apply Finset.sum_congr rfl
    intro n hn
    have hm : n + 1 < Multiplier.length j := by have := Finset.mem_range.mp hn; omega
    rw [margin_coefficients j hm, a1_eq, inverseTwo_eq hη, inverseThree_eq hη,
      realWInv_eq_rationalW, realWInv_eq_rationalW]
  rw [value_eq_formula]
  unfold formula
  rw [h1,h2]
  unfold largeTerms
  push_cast
  ring

/-- The reified C13 expression is a proved lower bound for the article's
actual Theta. Scalar numerical enclosures are displayed as premises here;
the final certificate discharges them rather than treating them as inputs. -/
theorem value_le_margin (j : Fin 7) (Jp : ℕ → ℝ)
    (hG : ((data j).gamma : ℝ) ≤ gammaG j)
    (hP : ((data j).prime : ℝ) ≤ primeLowerBudget j Jp)
    (hE : remainderE j ≤ 13) (hZ : zeroTailBudget j ≤ (1e-7 : ℝ))
    {L A : ℝ} (hb : InBand j L A) :
    value j (mu L) (eta L A) A ≤ margin j Jp L A := by
  obtain ⟨_,_,_,_,hη,hηmax,_,_,hμ⟩ := band_bounds j hb
  have ht := horner_moments_le_taylor hμ.le
  have hl := (abs_le.mp (largeTerms_rational_error j hμ hη hηmax)).1
  have hg := mul_le_mul_of_nonneg_right (add_le_add hG hP) (show 0 ≤ 10 * eta L A by positivity)
  have he := mul_le_mul_of_nonneg_right hE (pow_nonneg hη.le 3)
  rw [value_as_lower j (ne_of_gt hη), margin_q]
  unfold margin
  unfold largeTerms at hl ⊢
  nlinarith only [ht,hl,hg,he,hZ]

#print axioms value_le_margin
end Varlamov.MarginExpression
