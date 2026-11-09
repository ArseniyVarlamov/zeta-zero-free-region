import PrimeNumberTheoremAnd.IEANTN.Varlamov.Definitions
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import LeanCert.Tactic.IntervalAuto

/-!
# The exact polynomial smoothing kernel (Section 4, computer check C2)

The normalized polynomial is evaluated at x=u/d. This file checks the
rational construction inside Lean; a Python generator is not trusted.
-/

namespace Varlamov
namespace Kernel

open Real Polynomial
open scoped Polynomial

noncomputable def b : ℝ := -2409073 / 20000000
noncomputable def d : ℝ := 52698243 / 50000000
noncomputable def q (y : ℝ) : ℝ := (1 - y ^ 2) * (1 + b * y ^ 2)
noncomputable def qnorm : ℝ := 8116714872719329 / 7875000000000000

/-- The normalized polynomial piece w(d*x); all coefficients are exact. -/
noncomputable def unitPoly : ℝ[X] :=
  10 + C (-401678985597378570 / 8116714872719329) * X ^ 2
    + C (324912748355295450 / 8116714872719329) * X ^ 3
    + C (197487080515763640 / 8116714872719329) * X ^ 4
    + C (-226872255271059090 / 8116714872719329) * X ^ 5
    + C (25912844505277920 / 8116714872719329) * X ^ 7
    + C (-928581235092640 / 8116714872719329) * X ^ 9

noncomputable def unit (x : ℝ) : ℝ := unitPoly.eval x
noncomputable def piece (u : ℝ) : ℝ := unit (u / d)

lemma d_pos : 0 < d := by norm_num [d]
lemma qnorm_pos : 0 < qnorm := by norm_num [qnorm]
lemma b_range : -1 < b ∧ b < 0 := by norm_num [b]

lemma q_even (y : ℝ) : q (-y) = q y := by simp [q]
lemma q_zero : q 0 = 1 := by norm_num [q]
lemma q_one : q 1 = 0 := by norm_num [q]

lemma q_nonneg {y : ℝ} (hy : y ∈ Set.Icc (-1 : ℝ) 1) : 0 ≤ q y := by
  have hy2 : y ^ 2 ≤ 1 := by
    have hm := mul_nonneg (show 0 ≤ 1 - y by linarith [hy.2])
      (show 0 ≤ 1 + y by linarith [hy.1])
    nlinarith
  have hp : 0 ≤ 1 + b * y ^ 2 := by dsimp [b]; nlinarith [sq_nonneg y]
  exact mul_nonneg (by linarith) hp

lemma q_le_one {y : ℝ} (hy : y ∈ Set.Icc (-1 : ℝ) 1) : q y ≤ 1 := by
  have hy2 : y ^ 2 ≤ 1 := by
    have hm := mul_nonneg (show 0 ≤ 1 - y by linarith [hy.2])
      (show 0 ≤ 1 + y by linarith [hy.1])
    nlinarith
  have hb := b_range
  dsimp [q]
  nlinarith [sq_nonneg y, mul_nonpos_of_nonpos_of_nonneg hb.2.le (sq_nonneg y)]

lemma unit_zero : unit 0 = 10 := by norm_num [unit, unitPoly]
lemma unit_one : unit 1 = 0 := by norm_num [unit, unitPoly]
lemma unit_derivative_zero : unitPoly.derivative.eval 0 = 0 := by
  norm_num [unitPoly, Polynomial.derivative_pow]
lemma unit_derivative_one : unitPoly.derivative.eval 1 = 0 := by
  norm_num [unitPoly, Polynomial.derivative_pow]
lemma unit_derivative_two_one : unitPoly.derivative.derivative.eval 1 = 0 := by
  norm_num [unitPoly, Polynomial.derivative_pow]
lemma unit_derivative_two_zero_neg : unitPoly.derivative.derivative.eval 0 < 0 := by
  norm_num [unitPoly, Polynomial.derivative_pow]
lemma unit_derivative_three_zero_pos :
    unitPoly.derivative.derivative.derivative.eval 0 > 0 := by
  norm_num [unitPoly, Polynomial.derivative_pow]
lemma unit_derivative_three_endpoints :
    unitPoly.derivative.derivative.derivative.eval 1 =
      - unitPoly.derivative.derivative.derivative.eval 0 := by
  norm_num [unitPoly, Polynomial.derivative_pow]

lemma unit_nonneg : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ unit x := by
  simp only [unit, unitPoly, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow, Polynomial.eval_ofNat]
  bernstein_bound (trust := kernel)

lemma unit_le_ten : ∀ x ∈ Set.Icc (0 : ℝ) 1, unit x ≤ 10 := by
  simp only [unit, unitPoly, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow, Polynomial.eval_ofNat]
  bernstein_bound (trust := kernel)

noncomputable def unitD1 (x : ℝ) : ℝ :=
  (-803357971194757140 / 8116714872719329) * x
  + (974738245065886350 / 8116714872719329) * x ^ 2
  + (789948322063054560 / 8116714872719329) * x ^ 3
  + (-1134361276355295450 / 8116714872719329) * x ^ 4
  + (181389911536945440 / 8116714872719329) * x ^ 6
  + (-8357231115833760 / 8116714872719329) * x ^ 8

lemma unit_derivative_eval (x : ℝ) : unitPoly.derivative.eval x = unitD1 x := by
  norm_num [unitPoly, unitD1, Polynomial.derivative_pow]
  ring

lemma unit_derivative_nonpos :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, unitPoly.derivative.eval x ≤ 0 := by
  simp_rw [unit_derivative_eval]
  unfold unitD1
  bernstein_bound (trust := kernel)

lemma unit_antitone : AntitoneOn unit (Set.Icc (0 : ℝ) 1) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
    unitPoly.continuous.continuousOn unitPoly.differentiable.differentiableOn
  intro x hx
  rw [unitPoly.deriv]
  exact unit_derivative_nonpos x (interior_subset hx)

#print axioms unit_nonneg
#print axioms unit_antitone

end Kernel
end Varlamov
