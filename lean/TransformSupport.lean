import PrimeNumberTheoremAnd.IEANTN.Varlamov.ExactTransform
import PrimeNumberTheoremAnd.IEANTN.Varlamov.KernelSupport
import PrimeNumberTheoremAnd.ZetaConj

namespace Varlamov.Kernel
open Real MeasureTheory
open scoped ComplexConjugate

/-- The compact interval transform is exactly the one-sided Laplace transform
of the actual autocorrelation kernel, not just a polynomial surrogate. -/
theorem W_eq_one_sided (z : ℂ) :
    W z = ∫ u in Set.Ioi (0 : ℝ), Complex.exp (-z * (u : ℂ)) * (w u : ℂ) := by
  let f : ℝ → ℂ := fun u => Complex.exp (-z * (u : ℂ)) * (w u : ℂ)
  let g : ℝ → ℂ := (Set.Ioi (0 : ℝ)).indicator f
  have hs : Function.support g ⊆ Set.Ioc (0 : ℝ) d := by
    intro u hu
    have hn : g u ≠ 0 := hu
    have hpos : 0 < u := by
      by_contra h
      exact hn (by simp [g, Set.indicator_of_notMem, h])
    have hfn : f u ≠ 0 := by simpa [g, hpos] using hn
    have hud : u ≤ d := by
      by_contra h
      have hw := w_vanishes (show d ≤ |u| by rw [abs_of_pos hpos]; linarith)
      exact hfn (by simp [f, hw])
    exact ⟨hpos, hud⟩
  have hcomp : (∫ u in (0 : ℝ)..d, g u) = W z := by
    apply intervalIntegral.integral_congr_Ioo_of_le d_pos.le
    intro u hu
    change (Set.Ioi (0 : ℝ)).indicator f u = Complex.exp (-z * (u : ℂ)) * (piece u : ℂ)
    rw [Set.indicator_of_mem (show u ∈ Set.Ioi (0 : ℝ) from hu.1)]
    dsimp [f]
    rw [w_piece ⟨hu.1.le, hu.2.le⟩]
  rw [← hcomp, intervalIntegral.integral_eq_integral_of_support_subset hs]
  exact MeasureTheory.integral_indicator measurableSet_Ioi

lemma W_conj (z : ℂ) : W (conj z) = conj (W z) := by
  unfold W
  rw [← intervalIntegral_conj]
  apply intervalIntegral.integral_congr
  intro u _
  simp only [map_mul, ← Complex.exp_conj, map_neg, Complex.conj_ofReal, neg_mul]

#print axioms W_eq_one_sided
#print axioms W_conj

end Varlamov.Kernel
