import PrimeNumberTheoremAnd.IEANTN.Varlamov.PolynomialLaplace
import Mathlib.Tactic.ComputeDegree

namespace Varlamov.Kernel
open Polynomial MeasureTheory
open scoped Polynomial BigOperators

noncomputable def complexPoly : ℂ[X] :=
  (unitPoly.map Complex.ofRealHom).comp (C (1 / (d : ℂ)) * X)

lemma complexPoly_eval (u : ℝ) : complexPoly.eval (u : ℂ) = (piece u : ℂ) := by
  unfold complexPoly piece unit
  rw [Polynomial.eval_comp]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  rw [show (1 / (d : ℂ)) * (u : ℂ) = ((u / d : ℝ) : ℂ) from by push_cast; ring]
  exact Polynomial.eval_map_apply Complex.ofRealHom (u / d)

lemma complexPoly_degree : complexPoly.natDegree < 10 := by
  have hu : unitPoly.natDegree ≤ 9 := by
    unfold unitPoly
    compute_degree
  have hq : (C (1 / (d : ℂ)) * X).natDegree ≤ 1 := by
    calc
      _ ≤ (C (1 / (d : ℂ))).natDegree + (X : ℂ[X]).natDegree := natDegree_mul_le
      _ = 1 := by simp
  unfold complexPoly
  exact lt_of_le_of_lt
    (natDegree_comp_le.trans (Nat.mul_le_mul (natDegree_map_le.trans hu) hq)) (by norm_num)

/-- The actual one-sided transform of the polynomial smoothing kernel. -/
noncomputable def W (z : ℂ) : ℂ :=
  ∫ u in (0 : ℝ)..d, Complex.exp (-z * (u : ℂ)) * (piece u : ℂ)

@[blueprint "varlamov-exact-transform"
  (title := "Varlamov, Lemma 4.3: finite exact transform")
  (statement := /-- The transform of the polynomial kernel equals the finite sum of
  its endpoint derivatives divided by powers of z, for every nonzero complex z. -/)]
theorem W_exact {z : ℂ} (hz : z ≠ 0) :
    W z = ∑ k ∈ Finset.range 10,
      (((Polynomial.derivative^[k]) complexPoly).eval 0 -
        Complex.exp (-z * (d : ℂ)) * ((Polynomial.derivative^[k]) complexPoly).eval (d : ℂ)) /
          z ^ (k + 1) := by
  have h := polynomial_laplace_exact complexPoly complexPoly_degree hz d
  simpa only [W, complexPoly_eval] using h

#print axioms W_exact

end Varlamov.Kernel
