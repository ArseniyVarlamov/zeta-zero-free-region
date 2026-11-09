import PrimeNumberTheoremAnd.IEANTN.Varlamov.MarginExpression
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace Varlamov.MarginExpression
open LeanCert LeanCert.Core LeanCert.Engine

lemma range_correct (j : Fin 7) (b : List IntervalRat) (idx : ℕ) (lo hi : ℚ)
    (hc : checkRange j b idx lo hi = true) {ρ : ℕ → ℝ} (hρ : BoxEnvMem ρ b)
    {x : ℝ} (hx : x ∈ intervalEnvOfList b idx) :
    (lo : ℝ) ≤ deriv (Expr.evalAlong (expression j) ρ idx) x ∧
      deriv (Expr.evalAlong (expression j) ρ idx) x ≤ (hi : ℝ) := by
  unfold checkRange at hc
  cases he : LeanCert.evalWithDerivative (expression j) b idx options with
  | error err => simp [he] at hc
  | ok out =>
    rw [he] at hc
    have hq : lo ≤ out.derivative.lo ∧ out.derivative.hi ≤ hi := of_decide_eq_true hc
    have hm := (LeanCert.evalWithDerivative_correct he hρ hx).2
    have hlo : (lo : ℝ) ≤ (out.derivative.lo : ℝ) := by exact_mod_cast hq.1
    have hhi : (out.derivative.hi : ℝ) ≤ (hi : ℝ) := by exact_mod_cast hq.2
    exact ⟨hlo.trans hm.1, hm.2.trans hhi⟩

lemma positive_correct (j : Fin 7) (b : List IntervalRat) (c : ℚ)
    (hc : checkPositive j b c = true) {ρ : ℕ → ℝ} (hρ : BoxEnvMem ρ b) :
    (c : ℝ) < Expr.eval ρ (expression j) := by
  unfold checkPositive at hc
  cases he : LeanCert.evalWithDerivative (expression j) b 0 options with
  | error err => simp [he] at hc
  | ok out =>
    rw [he] at hc
    have hq : c < out.value.lo := of_decide_eq_true hc
    have hm := (LeanCert.evalWithDerivative_correct he hρ (hρ 0)).1
    exact lt_of_lt_of_le (by exact_mod_cast hq) hm.1

lemma sub_bounds_of_deriv {f : ℝ → ℝ} {a b lo hi : ℝ} (hab : a ≤ b) (hlo : 0 < lo)
    (hf : ∀ x ∈ Set.Icc a b, lo ≤ deriv f x ∧ deriv f x ≤ hi) :
    lo * (b - a) ≤ f b - f a ∧ f b - f a ≤ hi * (b - a) := by
  have hd (x : ℝ) (hx : x ∈ Set.Icc a b) : DifferentiableAt ℝ f x :=
    differentiableAt_of_deriv_ne_zero (ne_of_gt (hlo.trans_le (hf x hx).1))
  have hc : ContinuousOn f (Set.Icc a b) := fun x hx => (hd x hx).continuousAt.continuousWithinAt
  have hi' : DifferentiableOn ℝ f (interior (Set.Icc a b)) := fun x hx =>
    (hd x (interior_subset hx)).differentiableWithinAt
  exact ⟨(convex_Icc a b).mul_sub_le_image_sub_of_le_deriv hc hi'
    (fun x hx => (hf x (interior_subset hx)).1) a ⟨le_rfl,hab⟩ b ⟨hab,le_rfl⟩ hab,
    (convex_Icc a b).image_sub_le_mul_sub_of_deriv_le hc hi'
    (fun x hx => (hf x (interior_subset hx)).2) a ⟨le_rfl,hab⟩ b ⟨hab,le_rfl⟩ hab⟩

end Varlamov.MarginExpression
