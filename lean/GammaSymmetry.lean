import PrimeNumberTheoremAnd.IEANTN.Varlamov.GammaSeriesLimit
import Mathlib.Analysis.Calculus.Deriv.Star

namespace Varlamov.Kernel
open Complex
open scoped ComplexConjugate

/-- The short Mathlib argument also used by the private helper in KadiriEq15.
That private helper has no public lightweight import; this exposes the identity
without importing its full Perron/Wiener contour dependency tower. -/
lemma digamma_conjugation (z : ℂ) :
    Complex.digamma (conj z) = conj (Complex.digamma z) := by
  have hΓ : (starRingEnd ℂ) ∘ Gamma ∘ (starRingEnd ℂ) = Gamma := by
    funext w
    simp [Function.comp_apply, Gamma_conj]
  have hd : deriv Gamma (conj z) = conj (deriv Gamma z) := by
    conv_lhs => rw [← hΓ, deriv_conj_conj]
    simp [Function.comp_apply]
  rw [digamma_def, logDeriv_apply, logDeriv_apply, hd, Gamma_conj, ← map_div₀]

lemma Psi_line_real (y : ℝ) :
    Psi (gammaLine y) = ((Complex.digamma (gammaLine y / 2)).re : ℂ) := by
  have h1 : 1 - gammaLine y = conj (gammaLine y) := by
    apply Complex.ext <;> norm_num [gammaLine]
  have hc : (1 - gammaLine y) / 2 = conj (gammaLine y / 2) := by rw [map_div₀, map_ofNat, h1]
  unfold Psi
  rw [hc, digamma_conjugation, Complex.add_conj]
  push_cast
  ring

#print axioms Psi_line_real

end Varlamov.Kernel
