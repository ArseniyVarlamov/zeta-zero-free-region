import PrimeNumberTheoremAnd.IEANTN.Varlamov.KernelIntegral
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! # Finite exact Laplace transform, Lemma 4.3

This uses an explicit antiderivative and the fundamental theorem of calculus.
It applies to any polynomial, with no analytic theorem assumed as an axiom.
-/

namespace Varlamov.Kernel
open Polynomial MeasureTheory
open scoped BigOperators

noncomputable def laplaceTail (p : ℂ[X]) (z : ℂ) (n : ℕ) (u : ℂ) : ℂ :=
  ∑ k ∈ Finset.range n, ((Polynomial.derivative^[k]) p).eval u / z ^ (k + 1)

lemma tail_cancel (a : ℕ → ℂ) {z : ℂ} (hz : z ≠ 0) (n : ℕ) :
    z * (∑ k ∈ Finset.range n, a k / z ^ (k + 1)) -
      (∑ k ∈ Finset.range n, a (k + 1) / z ^ (k + 1)) = a 0 - a n / z ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hm : z * (a n / z ^ (n + 1)) = a n / z ^ n := by
        rw [pow_succ]
        field_simp
        
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      calc
        z * ((∑ k ∈ Finset.range n, a k / z ^ (k + 1)) + a n / z ^ (n + 1)) -
            ((∑ k ∈ Finset.range n, a (k + 1) / z ^ (k + 1)) + a (n + 1) / z ^ (n + 1)) =
          (z * (∑ k ∈ Finset.range n, a k / z ^ (k + 1)) -
            (∑ k ∈ Finset.range n, a (k + 1) / z ^ (k + 1))) +
              z * (a n / z ^ (n + 1)) - a (n + 1) / z ^ (n + 1) := by ring
        _ = a 0 - a (n + 1) / z ^ (n + 1) := by rw [ih, hm]; ring

lemma laplaceTail_hasDerivAt (p : ℂ[X]) (z u : ℂ) (n : ℕ) :
    HasDerivAt (laplaceTail p z n)
      (∑ k ∈ Finset.range n, ((Polynomial.derivative^[k + 1]) p).eval u / z ^ (k + 1)) u := by
  apply HasDerivAt.fun_sum
  intro k _
  simpa only [Function.iterate_succ_apply'] using
    (((Polynomial.derivative^[k]) p).hasDerivAt u).div_const (z ^ (k + 1))

noncomputable def laplacePrimitive (p : ℂ[X]) (z : ℂ) (n : ℕ) (u : ℂ) : ℂ :=
  - Complex.exp (-z * u) * laplaceTail p z n u

lemma laplacePrimitive_hasDerivAt (p : ℂ[X]) {z : ℂ} (hz : z ≠ 0)
    {n : ℕ} (hp : (Polynomial.derivative^[n]) p = 0) (u : ℂ) :
    HasDerivAt (laplacePrimitive p z n) (Complex.exp (-z * u) * p.eval u) u := by
  have he := (((hasDerivAt_id u).const_mul (-z)).cexp).neg
  have ht := laplaceTail_hasDerivAt p z u n
  have hc := tail_cancel (fun k => ((Polynomial.derivative^[k]) p).eval u) hz n
  simp only [hp, Polynomial.eval_zero, zero_div, sub_zero, Function.iterate_zero,
    id_eq] at hc
  change z * laplaceTail p z n u -
    (∑ k ∈ Finset.range n, ((Polynomial.derivative^[k + 1]) p).eval u / z ^ (k + 1)) = p.eval u at hc
  convert he.mul ht using 1
  · rfl
  · rw [← hc]
    dsimp
    ring

/-- A polynomial of degree less than n has a finite exact Laplace transform. -/
theorem polynomial_laplace_exact (p : ℂ[X]) {n : ℕ} (hp : p.natDegree < n)
    {z : ℂ} (hz : z ≠ 0) (d : ℝ) :
    (∫ u in (0 : ℝ)..d, Complex.exp (-z * (u : ℂ)) * p.eval (u : ℂ)) =
      ∑ k ∈ Finset.range n,
        (((Polynomial.derivative^[k]) p).eval 0 -
          Complex.exp (-z * (d : ℂ)) * ((Polynomial.derivative^[k]) p).eval (d : ℂ)) /
            z ^ (k + 1) := by
  have hp0 : (Polynomial.derivative^[n]) p = 0 := Polynomial.iterate_derivative_eq_zero hp
  have hi : IntervalIntegrable
      (fun u : ℝ => Complex.exp (-z * (u : ℂ)) * p.eval (u : ℂ)) volume 0 d := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ => (laplacePrimitive_hasDerivAt p hz hp0 (u : ℂ)).comp_ofReal) hi]
  unfold laplacePrimitive laplaceTail
  simp only [Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero, neg_mul,
    one_mul, sub_neg_eq_add, sub_div, mul_div_assoc, Finset.sum_sub_distrib]
  rw [← Finset.mul_sum]
  ring

#print axioms polynomial_laplace_exact

end Varlamov.Kernel
