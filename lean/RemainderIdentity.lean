import PrimeNumberTheoremAnd.IEANTN.Varlamov.TrivialZeroSeries
import PrimeNumberTheoremAnd.IEANTN.Varlamov.GammaSymmetry
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace Varlamov.Kernel
open Real MeasureTheory Filter Topology
open scoped BigOperators

lemma continuous_Psi_line : Continuous (fun y : ℝ => Psi (gammaLine y)) := by
  have ha : Continuous (fun y : ℝ => gammaLine y / 2) := by unfold gammaLine; fun_prop
  have hp : Continuous (fun y : ℝ => Complex.digamma (gammaLine y / 2)) := by
    apply continuous_iff_continuousAt.mpr
    intro y
    exact (Complex.continuousAt_digamma_of_re_pos
      (by norm_num [gammaLine, Complex.div_re, Complex.normSq_apply])).comp ha.continuousAt
  have hr : Continuous (fun y : ℝ => ((Complex.digamma (gammaLine y / 2)).re : ℂ)) :=
    Complex.continuous_ofReal.comp (Complex.continuous_re.comp hp)
  simpa only [Psi_line_real] using hr

/-- The finite gamma projections converge under an integrable dominator.
The only external premise is the explicitly cited classical Cauchy formula. -/
theorem archimedean_projection (hC : HalfPlaneCauchyInput) {η : ℝ} {s : ℂ}
    (hη : 0 < η) (hs : (1 / 2 : ℝ) < s.re) :
    Integrable (fun y : ℝ => lineWeight η s y * Psi (gammaLine y)) ∧
      lineNorm * (∫ y : ℝ, lineWeight η s y * Psi (gammaLine y)) =
        - (∑' n : ℕ, zeroSample η s n) := by
  let f : ℝ → ℂ := fun y => lineWeight η s y * Psi (gammaLine y)
  let F : ℕ → ℝ → ℂ := fun N y => lineWeight η s y * psiPartial N (gammaLine y)
  let E : ℕ → ℝ → ℂ := fun N => F N - f
  let bound : ℝ → ℝ := fun y => 12 * ((1 + |y|) * ‖lineWeight η s y‖)
  have hF (N : ℕ) : Integrable (F N) := (gamma_partial_projection hC hη hs N).1
  have hfc : Continuous f := (continuous_lineWeight hη hs).mul continuous_Psi_line
  have hEmeas (N : ℕ) : AEStronglyMeasurable (E N) :=
    (hF N).aestronglyMeasurable.sub hfc.aestronglyMeasurable
  have hb : Integrable bound := (weighted_line_integrable hη hs).const_mul 12
  have hErr (N : ℕ) (hN : 1 ≤ N) (y : ℝ) : ‖E N y‖ ≤ bound y := by
    have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hNp : (0 : ℝ) < N := by linarith
    have hdiv : 12 * (1 + |y|) / (N : ℝ) ≤ 12 * (1 + |y|) := by
      apply (div_le_iff₀ hNp).mpr
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hNR (show 0 ≤ 12 * (1 + |y|) by positivity)
    have he : E N y = -(lineWeight η s y * (Psi (gammaLine y) - psiPartial N (gammaLine y))) := by
      simp only [E, F, f, Pi.sub_apply]
      ring
    rw [he, norm_neg, norm_mul]
    calc
      _ ≤ ‖lineWeight η s y‖ * (12 * (1 + |y|) / (N : ℝ)) :=
        mul_le_mul_of_nonneg_left (psiPartial_line_error y hN) (norm_nonneg _)
      _ ≤ ‖lineWeight η s y‖ * (12 * (1 + |y|)) := mul_le_mul_of_nonneg_left hdiv (norm_nonneg _)
      _ = bound y := by dsimp [bound]; ring
  have hE1 : Integrable (E 1) := hb.mono' (hEmeas 1)
    (Filter.Eventually.of_forall (fun y => hErr 1 (by decide) y))
  have hf : Integrable f := ((hF 1).sub hE1).congr (Filter.Eventually.of_forall (fun y => by
    simp only [E, Pi.sub_apply]
    ring))
  let Dom : ℝ → ℝ := bound + (fun y => ‖f y‖)
  have hDom : Integrable Dom := hb.add hf.norm
  have hBound : ∀ᶠ N : ℕ in atTop, ∀ᵐ y : ℝ, ‖F N y‖ ≤ Dom y := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    apply Filter.Eventually.of_forall
    intro y
    have he : F N y = E N y + f y := by simp only [E, Pi.sub_apply]; ring
    change ‖F N y‖ ≤ bound y + ‖f y‖
    calc
      _ ≤ ‖E N y‖ + ‖f y‖ := (congrArg norm he).trans_le (norm_add_le _ _)
      _ ≤ _ := add_le_add (hErr N hN y) le_rfl
  have hLim : ∀ᵐ y : ℝ, Tendsto (fun N : ℕ => F N y) atTop (𝓝 (f y)) := by
    apply Filter.Eventually.of_forall
    intro y
    exact tendsto_const_nhds.mul (psiPartial_line_tendsto y)
  have hInt : Tendsto (fun N : ℕ => ∫ y : ℝ, F N y) atTop (𝓝 (∫ y : ℝ, f y)) :=
    tendsto_integral_filter_of_dominated_convergence Dom
      (Filter.Eventually.of_forall (fun N => (hF N).aestronglyMeasurable)) hBound hDom hLim
  have hLeft : Tendsto (fun N : ℕ => lineNorm * (∫ y : ℝ, F N y)) atTop
      (𝓝 (lineNorm * (∫ y : ℝ, f y))) := tendsto_const_nhds.mul hInt
  have heq : (fun N : ℕ => lineNorm * (∫ y : ℝ, F N y)) =
      (fun N : ℕ => -(∑ n ∈ Finset.range N, zeroSample η s n)) := by
    funext N
    exact (gamma_partial_projection hC hη hs N).2
  rw [heq] at hLeft
  have hRight := (zeroSample_summable hη hs).hasSum.tendsto_sum_nat.neg
  exact ⟨hf, tendsto_nhds_unique hLeft hRight⟩

/-- Kadiri's remainder, parametrized upward on Re z=1/2. The line differential
cancels the i in 1/(2*pi*i), leaving lineNorm=1/(2*pi). -/
noncomputable def Delta (η : ℝ) (s : ℂ) : ℂ :=
  lineNorm * (∫ y : ℝ, lineWeight η s y * ((Complex.digamma (gammaLine y / 2)).re : ℂ)) + W0 (s / (η : ℂ))

@[blueprint "varlamov-trivial-zero-remainder"
  (title := "Varlamov, Proposition 6.3: remainder over the trivial zeros")
  (statement := /-- If eta is positive and $\Re s>1/2$, Kadiri's remainder is
  $-\sum_{n\ge1}W_0((s+2n)/\eta)$, and the series converges absolutely.
  The generic classical half-plane Cauchy formula is an explicit published
  input; all kernel, approximation and limiting arguments are proved here. -/)
  (uses := ["varlamov-transform-right-bound", "varlamov-digamma-growth"])]
theorem Delta_trivial_zeros (hC : HalfPlaneCauchyInput) {η : ℝ} {s : ℂ}
    (hη : 0 < η) (hs : (1 / 2 : ℝ) < s.re) :
    Summable (fun n : ℕ => ‖zeroSample η s (n + 1)‖) ∧
      Delta η s = -(∑' n : ℕ, zeroSample η s (n + 1)) := by
  have hNorm := (summable_nat_add_iff 1).mpr (zeroSample_norm_summable hη hs)
  refine ⟨hNorm, ?_⟩
  have hp := (archimedean_projection hC hη hs).2
  simp_rw [Psi_line_real] at hp
  unfold Delta
  rw [hp, (zeroSample_summable hη hs).tsum_eq_zero_add]
  simp only [zeroSample, Nat.cast_zero, mul_zero, add_zero]
  ring

#print axioms archimedean_projection
#print axioms Delta_trivial_zeros

end Varlamov.Kernel
