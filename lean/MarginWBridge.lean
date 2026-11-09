import PrimeNumberTheoremAnd.IEANTN.Varlamov.MarginExpressionSemantics

namespace Varlamov.MarginExpression
open Real Polynomial
open scoped BigOperators

lemma a1_eq : (a1 : ℝ) = Trigonometric.a 1 := by norm_num [a1, Trigonometric.a]

-- Exact normalization of the degree-nine endpoint derivatives requires a
-- larger heartbeat allowance than a small symbolic arithmetic lemma.
set_option maxHeartbeats 3000000 in
lemma realWInv_eq_rationalW (z : ℝ) : realWInv z⁻¹ = Varlamov.rationalW z := by
  by_cases hz : z = 0
  · subst z
    simp [realWInv, inverseHorner, unitLeft, Varlamov.rationalW, pow_succ]
  · norm_num [realWInv, inverseHorner, unitLeft, d, Varlamov.rationalW,
      Varlamov.unitLeft, Kernel.unitPoly, Kernel.d, Finset.sum_range_succ,
      Function.iterate_succ_apply', Polynomial.derivative_pow]
    field_simp
    <;> ring

lemma inverseOne_eq {μ η : ℝ} (hη : η ≠ 0) (m : ℕ) :
    inverseOneReal μ η m = (argumentOne μ η m)⁻¹ := by
  have he : argumentOne μ η m =
      (((m : ℝ) + 1) - ((2 * (m : ℝ) + 1) * μ + 1) * η) / η := by
    unfold argumentOne
    field_simp
    <;> ring
  rw [he, inv_div]
  rfl

lemma inverseTwo_eq {μ η : ℝ} (hη : η ≠ 0) (m : ℕ) :
    inverseTwoReal μ η m = (argumentTwo μ η m)⁻¹ := by
  have he : argumentTwo μ η m =
      ((m : ℝ) - ((2 * (m : ℝ) + 1) * μ - 1) * η) / η := by
    unfold argumentTwo
    field_simp
    <;> ring
  rw [he, inv_div]
  rfl

lemma inverseThree_eq {μ η : ℝ} (hη : η ≠ 0) (m : ℕ) :
    inverseThreeReal μ η m = (argumentThree μ η m)⁻¹ := by
  have he : argumentThree μ η m =
      ((m : ℝ) - (2 * (m : ℝ) + 1) * μ * η) / η := by
    unfold argumentThree
    field_simp
    <;> ring
  rw [he, inv_div]
  rfl

#print axioms realWInv_eq_rationalW
end Varlamov.MarginExpression
