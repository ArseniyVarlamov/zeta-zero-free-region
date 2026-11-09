import PrimeNumberTheoremAnd.IEANTN.Varlamov.TransformSupport
import Mathlib.Analysis.Calculus.ParametricIntegral

namespace Varlamov.Kernel
open Real MeasureTheory Topology

/-- The Laplace transform is entire; compactness supplies a uniform dominator
for differentiation under the integral. -/
theorem differentiable_W : Differentiable ℂ W := by
  intro z₀
  let μ : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) d)
  let : IsFiniteMeasure μ := by dsimp [μ]; infer_instance
  let F : ℂ → ℝ → ℂ := fun z u => Complex.exp (-z * (u : ℂ)) * (piece u : ℂ)
  let D : ℂ → ℝ → ℂ := fun z u => -(u : ℂ) * Complex.exp (-z * (u : ℂ)) * (piece u : ℂ)
  have hFcont : Continuous (fun p : ℂ × ℝ => F p.1 p.2) := by
    dsimp [F, piece, unit]
    fun_prop
  have hDcont : Continuous (fun p : ℂ × ℝ => D p.1 p.2) := by
    dsimp [D, piece, unit]
    fun_prop
  let S : Set (ℂ × ℝ) := Metric.closedBall z₀ 1 ×ˢ Set.Icc (0 : ℝ) d
  have hS : IsCompact S := (isCompact_closedBall z₀ 1).prod isCompact_Icc
  obtain ⟨C, hC⟩ := hS.bddAbove_image hDcont.norm.continuousOn
  have hmem : ∀ᵐ u ∂μ, u ∈ Set.Ioc (0 : ℝ) d := by
    dsimp [μ]
    exact ae_restrict_mem measurableSet_Ioc
  have hFmeas : ∀ᶠ z in 𝓝 z₀, AEStronglyMeasurable (F z) μ := by
    apply Filter.Eventually.of_forall
    intro z
    have hc : Continuous (F z) := by dsimp [F, piece, unit]; fun_prop
    exact hc.aestronglyMeasurable
  have hFint : Integrable (F z₀) μ := by
    have hc : Continuous (F z₀) := by dsimp [F, piece, unit]; fun_prop
    exact (hc.intervalIntegrable 0 d).1
  have hDmeas : AEStronglyMeasurable (D z₀) μ := by
    have hc : Continuous (D z₀) := by dsimp [D, piece, unit]; fun_prop
    exact hc.aestronglyMeasurable
  have hbound : ∀ᵐ u ∂μ, ∀ z ∈ Metric.ball z₀ 1, ‖D z u‖ ≤ C := by
    filter_upwards [hmem] with u hu
    intro z hz
    apply hC
    exact ⟨(z,u), ⟨Metric.ball_subset_closedBall hz, ⟨hu.1.le, hu.2⟩⟩, rfl⟩
  have hdiff : ∀ᵐ u ∂μ, ∀ z ∈ Metric.ball z₀ 1, HasDerivAt (F · u) (D z u) z := by
    apply Filter.Eventually.of_forall
    intro u z _
    have h := (((hasDerivAt_id z).mul_const (-(u : ℂ))).cexp).mul_const (piece u : ℂ)
    simpa only [F, D, id_eq, one_mul, mul_neg, neg_mul, mul_comm, mul_left_comm, mul_assoc] using h
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (F := F) (F' := D) (s := Metric.ball z₀ 1) (bound := fun _ => C)
    (Metric.ball_mem_nhds z₀ (by norm_num : (0 : ℝ) < 1))
    hFmeas hFint hDmeas hbound (integrable_const C) hdiff
  change DifferentiableAt ℂ
    (fun z : ℂ => ∫ u in (0 : ℝ)..d, Complex.exp (-z * (u : ℂ)) * (piece u : ℂ)) z₀
  simp_rw [intervalIntegral.integral_of_le d_pos.le]
  exact h.2.differentiableAt

#print axioms differentiable_W

end Varlamov.Kernel
