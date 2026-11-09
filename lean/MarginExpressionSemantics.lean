import PrimeNumberTheoremAnd.IEANTN.Varlamov.MarginExpression
import PrimeNumberTheoremAnd.IEANTN.Varlamov.RealTransformCertificate

namespace Varlamov.MarginExpression
open LeanCert LeanCert.Core
open scoped BigOperators

noncomputable def horner (cs : List ℚ) (x : ℝ) : ℝ :=
  cs.foldr (fun c acc => (c : ℝ) + x * acc) 0
noncomputable def inverseHorner (cs : List ℚ) (x : ℝ) : ℝ :=
  cs.foldr (fun c acc => ((c : ℝ) + acc) * x) 0
noncomputable def realWInv (x : ℝ) : ℝ := (d : ℝ) * inverseHorner unitLeft (x / (d : ℝ))

lemma eval_horner (ρ : ℕ → ℝ) (cs : List ℚ) (v : Expr) :
    Expr.eval ρ (cs.foldr (fun c acc => add (q c) (mul v acc)) (q 0)) =
      horner cs (Expr.eval ρ v) := by
  induction cs with
  | nil => simp [horner, q, Expr.eval]
  | cons c cs ih => simpa [horner, add, mul, q, Expr.eval] using congrArg (fun t : ℝ => (c : ℝ) + Expr.eval ρ v * t) ih

lemma eval_inverseHorner (ρ : ℕ → ℝ) (cs : List ℚ) (v : Expr) :
    Expr.eval ρ (cs.foldr (fun c acc => mul (add (q c) acc) v) (q 0)) =
      inverseHorner cs (Expr.eval ρ v) := by
  induction cs with
  | nil => simp [inverseHorner, q, Expr.eval]
  | cons c cs ih => simpa [inverseHorner, add, mul, q, Expr.eval] using congrArg (fun t : ℝ => ((c : ℝ) + t) * Expr.eval ρ v) ih

lemma eval_horner_raw (ρ : ℕ → ℝ) (cs : List ℚ) (v : Expr) :
    Expr.eval ρ (cs.foldr (fun c acc => Expr.add (Expr.const c) (Expr.mul v acc)) (Expr.const 0)) =
      horner cs (Expr.eval ρ v) := eval_horner ρ cs v

lemma eval_inverseHorner_raw (ρ : ℕ → ℝ) (cs : List ℚ) (v : Expr) :
    Expr.eval ρ (cs.foldr (fun c acc => Expr.mul (Expr.add (Expr.const c) acc) v) (Expr.const 0)) =
      inverseHorner cs (Expr.eval ρ v) := eval_inverseHorner ρ cs v

@[simp] lemma eval_rationalWInv (ρ : ℕ → ℝ) (v : Expr) :
    Expr.eval ρ (rationalWInv v) = realWInv (Expr.eval ρ v) := by
  unfold rationalWInv realWInv
  simp only [mul, add, Expr.eval_mul, q, Expr.eval_const, div, Expr.eval_inv,
    eval_inverseHorner_raw, div_eq_mul_inv]

@[simp] lemma eval_sumRange (ρ : ℕ → ℝ) (n : ℕ) (f : ℕ → Expr) :
    Expr.eval ρ (sumRange n f) = ∑ k ∈ Finset.range n, Expr.eval ρ (f k) := by
  induction n with
  | zero => simp [sumRange, q, Expr.eval]
  | succ n ih => simp [sumRange, add, Expr.eval, ih, Finset.sum_range_succ]

noncomputable def inverseOneReal (μ η : ℝ) (m : ℕ) : ℝ :=
  η / (((m : ℝ) + 1) - ((2 * (m : ℝ) + 1) * μ + 1) * η)
noncomputable def inverseTwoReal (μ η : ℝ) (m : ℕ) : ℝ :=
  η / ((m : ℝ) - ((2 * (m : ℝ) + 1) * μ - 1) * η)
noncomputable def inverseThreeReal (μ η : ℝ) (m : ℕ) : ℝ :=
  η / ((m : ℝ) - (2 * (m : ℝ) + 1) * μ * η)

@[simp] lemma eval_inverseOne (ρ : ℕ → ℝ) (μ η : Expr) (m : ℕ) :
    Expr.eval ρ (inverseOne μ η m) = inverseOneReal (Expr.eval ρ μ) (Expr.eval ρ η) m := by
  simp [inverseOne, inverseOneReal, div, sub, add, mul, q, Expr.eval, div_eq_mul_inv, sub_eq_add_neg]

@[simp] lemma eval_inverseTwo (ρ : ℕ → ℝ) (μ η : Expr) (m : ℕ) :
    Expr.eval ρ (inverseTwo μ η m) = inverseTwoReal (Expr.eval ρ μ) (Expr.eval ρ η) m := by
  simp [inverseTwo, inverseTwoReal, div, sub, add, mul, q, Expr.eval, div_eq_mul_inv, sub_eq_add_neg]

@[simp] lemma eval_inverseThree (ρ : ℕ → ℝ) (μ η : Expr) (m : ℕ) :
    Expr.eval ρ (inverseThree μ η m) = inverseThreeReal (Expr.eval ρ μ) (Expr.eval ρ η) m := by
  simp [inverseThree, inverseThreeReal, div, sub, add, mul, q, Expr.eval, mul_assoc, div_eq_mul_inv, sub_eq_add_neg]

noncomputable def formula (j : Fin 7) (μ η A : ℝ) : ℝ :=
  horner moments (μ - 1) +
  (∑ m ∈ Finset.range (data j).coeffs.length,
    ((a1 * (data j).coeffs.getD m 0 : ℚ) : ℝ) * realWInv (inverseOneReal μ η m)) +
  (∑ n ∈ Finset.range ((data j).coeffs.length - 1),
    (((data j).coeffs.getD (n + 1) 0 : ℚ) : ℝ) *
      ((a1 : ℝ) * realWInv (inverseTwoReal μ η (n + 1)) - realWInv (inverseThreeReal μ η (n + 1)))) +
  ((10*((data j).gamma+(data j).prime)-1/10000000000 : ℚ) : ℝ) * η -
  (13 * η ^ 3 + (1/10000000+1/1000000000000+1/100000000000000000 : ℚ) + ((data j).q : ℝ) * A)

lemma value_eq_formula (j : Fin 7) (μ η A : ℝ) : value j μ η A = formula j μ η A := by
  unfold value expression formula
  simp only [add, sub, mul, q, Expr.eval_add, Expr.eval_mul, Expr.eval_neg, Expr.eval_const,
    Expr.eval_var, eval_sumRange, eval_rationalWInv, eval_inverseOne, eval_inverseTwo,
    eval_inverseThree, eval_horner_raw]
  simp [environment]
  ring

lemma value_affine_A (j : Fin 7) (μ η A B : ℝ) :
    value j μ η A = value j μ η B + ((data j).q : ℝ) * (B - A) := by
  rw [value_eq_formula, value_eq_formula]
  unfold formula
  ring

end Varlamov.MarginExpression
