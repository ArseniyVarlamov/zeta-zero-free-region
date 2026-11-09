import PrimeNumberTheoremAnd.IEANTN.Varlamov.CheckedDerivatives

namespace Varlamov.MarginExpression
open LeanCert LeanCert.Core LeanCert.Engine

lemma fullBox_mem (j : Fin 7) {μ η A : ℝ}
    (hμ : μ ∈ Set.Icc (9 / 10 : ℝ) 1)
    (hη : η ∈ Set.Icc (1 / (6 * bandHi j)) (etaMax j))
    (hA : A ∈ Set.Icc (1 / 6 : ℝ) Astar) :
    BoxEnvMem (environment μ η A) (fullBox j) := by
  intro i
  rcases i with _ | i
  · fin_cases j <;> simpa [environment, fullBox, IntervalRat.mem_def] using hμ
  rcases i with _ | i
  · fin_cases j <;> simpa [environment, fullBox, IntervalRat.mem_def, bandHi, etaMax] using hη
  rcases i with _ | i
  · fin_cases j <;> simpa [environment, fullBox, IntervalRat.mem_def, Astar] using hA
  · fin_cases j <;> simp [environment, fullBox, IntervalRat.mem_def, IntervalRat.singleton]

lemma along_mu (j : Fin 7) (μ η A : ℝ) :
    Expr.evalAlong (expression j) (environment μ η A) 0 = fun x => value j x η A := by
  funext x
  apply congrArg (fun ρ : ℕ → ℝ => Expr.eval ρ (expression j))
  funext i
  by_cases h0 : i = 0
  · subst i; simp [Expr.updateVar, environment]
  · simp [Expr.updateVar, environment, h0]

lemma along_eta (j : Fin 7) (μ η A : ℝ) :
    Expr.evalAlong (expression j) (environment μ η A) 1 = fun x => value j μ x A := by
  funext x
  apply congrArg (fun ρ : ℕ → ℝ => Expr.eval ρ (expression j))
  funext i
  by_cases h0 : i = 0
  · subst i; simp [Expr.updateVar, environment]
  · by_cases h1 : i = 1
    · subst i; simp [Expr.updateVar, environment]
    · simp [Expr.updateVar, environment, h0, h1]

lemma mu_derivative_bounds (j : Fin 7)
    (hc : checkRange j (fullBox j) 0 (1/10) (1/2) = true)
    {μ η A x : ℝ} (hμ : μ ∈ Set.Icc (9 / 10 : ℝ) 1)
    (hη : η ∈ Set.Icc (1 / (6 * bandHi j)) (etaMax j))
    (hA : A ∈ Set.Icc (1 / 6 : ℝ) Astar) (hx : x ∈ Set.Icc (9 / 10 : ℝ) 1) :
    (1/10 : ℝ) ≤ deriv (fun y => value j y η A) x ∧
      deriv (fun y => value j y η A) x ≤ (1/2 : ℝ) := by
  have hρ := fullBox_mem j hμ hη hA
  have hx' := fullBox_mem j hx hη hA 0
  simp only [environment, ↓reduceIte] at hx'
  have hr := range_correct j (fullBox j) 0 (1/10) (1/2) hc hρ hx'
  rw [along_mu] at hr
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hr
  exact hr

lemma eta_derivative_bounds (j : Fin 7)
    (hc : checkRange j (fullBox j) 1 8 50 = true)
    {μ η A x : ℝ} (hμ : μ ∈ Set.Icc (9 / 10 : ℝ) 1)
    (hη : η ∈ Set.Icc (1 / (6 * bandHi j)) (etaMax j))
    (hA : A ∈ Set.Icc (1 / 6 : ℝ) Astar)
    (hx : x ∈ Set.Icc (1 / (6 * bandHi j)) (etaMax j)) :
    (8 : ℝ) ≤ deriv (fun y => value j μ y A) x ∧
      deriv (fun y => value j μ y A) x ≤ (50 : ℝ) := by
  have hρ := fullBox_mem j hμ hη hA
  have hx' := fullBox_mem j hμ hx hA 1
  norm_num only [environment, ↓reduceIte] at hx'
  have hr := range_correct j (fullBox j) 1 8 50 hc hρ hx'
  rw [along_eta] at hr
  norm_num only [Rat.cast_ofNat] at hr
  exact hr

end Varlamov.MarginExpression
