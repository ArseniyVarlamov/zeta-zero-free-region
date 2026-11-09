import PrimeNumberTheoremAnd.IEANTN.Varlamov.SmoothTestKernel
import PrimeNumberTheoremAnd.IEANTN.Varlamov.RemainderIdentity

/-!
# Published explicit-formula input

H. Kadiri, Une region explicite sans zeros pour la fonction zeta de Riemann,
Acta Arithmetica 117 (2005), 303--339, Proposition 2.1, equation (7), p.308;
proof and extension on pp.314--317. https://doi.org/10.4064/aa117-4-1

The published statement says "soit s un nombre complexe". We specialize to
Re(s)>1/2, where the remainder integral below has no pole on its contour.
The input is a theorem parameter, not an axiom. Its test functions have a
stronger global C2 extension; only nonnegative arguments enter the formula.
Zero sums use PNT+'s multiplicity-weighted convention, not a sum over distinct
zeros without their orders.
-/

namespace Varlamov
open Real MeasureTheory
open scoped BigOperators

structure SmoothKadiriAdmissible (D : ℝ) (f : ℝ → ℝ) : Prop where
  D_pos : 0 < D
  nonneg : ∀ u : ℝ, 0 ≤ u → 0 ≤ f u
  smooth : ContDiff ℝ 2 f
  zero_after : ∀ u : ℝ, D ≤ u → f u = 0
  first_zero : deriv f 0 = 0
  first_end : deriv f D = 0
  second_end : deriv (deriv f) D = 0

noncomputable def gammaTerm (s : ℂ) : ℝ :=
  - (1 / 2) * Real.log Real.pi + (1 / 2) * (Complex.digamma (s / 2 + 1)).re
noncomputable def primeTerm (f : ℝ → ℝ) (s : ℂ) (n : ℕ) : ℂ :=
  (ArithmeticFunction.vonMangoldt n : ℂ) / (n : ℂ) ^ s * (f (Real.log n) : ℂ)
noncomputable def primeSum (f : ℝ → ℝ) (s : ℂ) : ℝ := (∑' n : ℕ, primeTerm f s n).re
noncomputable def rawRemainder (f : ℝ → ℝ) (s : ℂ) : ℂ :=
  Kernel.lineNorm * (∫ y : ℝ,
    (Kernel.laplace (deriv (deriv f)) (s - Kernel.gammaLine y) / (s - Kernel.gammaLine y) ^ 2) *
      ((Complex.digamma (Kernel.gammaLine y / 2)).re : ℂ)) +
    Kernel.laplace (deriv (deriv f)) s / s ^ 2

/-- Kadiri Proposition 2.1, equation (7), with absolute convergence of its
multiplicity-weighted real zero sum, as used in the published derivation. -/
def KadiriExplicitInput : Prop :=
  ∀ D : ℝ, ∀ f : ℝ → ℝ, SmoothKadiriAdmissible D f → ∀ s : ℂ, (1 / 2 : ℝ) < s.re →
    Summable (fun ρ : riemannZeta.zeroes_rect (Set.Ioo 0 1) Set.univ =>
      (Kernel.laplace f (s - (ρ : ℂ))).re * (riemannZeta.order (ρ : ℂ) : ℝ)) ∧
    primeSum f s = f 0 * gammaTerm s + (Kernel.laplace f (s - 1)).re -
      riemannZeta.zeroes_sum (Set.Ioo 0 1) Set.univ (fun ρ => (Kernel.laplace f (s - ρ)).re) +
      (rawRemainder f s).re

namespace Kernel
lemma smooth_admissible {η : ℝ} (hη : 0 < η) :
    SmoothKadiriAdmissible (d / η + 1) (smoothKernel η) := by
  have hD : 0 < d / η + 1 := add_pos (div_pos d_pos hη) zero_lt_one
  have hlarge : d / η < d / η + 1 := by linarith
  refine ⟨hD, ?_, smoothKernel_contDiff η, ?_, ?_, ?_, ?_⟩
  · intro u hu
    rw [smoothKernel_eq_g hη hu]
    exact g_nonneg hη.le u
  · intro u hu
    exact smoothDerivative_zero_of_gt 0 hη (by linarith)
  · rw [smoothKernel_deriv]
    have hp := piece_first_zero
    rw [iteratedDeriv_piece] at hp
    simp only [smoothDerivative, mul_zero, cut_of_le d_pos.le, hp, mul_zero]
  · rw [smoothKernel_deriv]
    exact smoothDerivative_zero_of_gt 1 hη hlarge
  · rw [smoothKernel_second]
    exact smoothDerivative_zero_of_gt 2 hη hlarge

lemma smoothKernel_zero {η : ℝ} (hη : 0 < η) : smoothKernel η 0 = 10 * η := by
  rw [smoothKernel_eq_g hη le_rfl, g_zero]

lemma rawRemainder_smooth {η : ℝ} {s : ℂ} (hη : 0 < η) (hs : (1 / 2 : ℝ) < s.re) :
    rawRemainder (smoothKernel η) s = Delta η s := by
  have hs0 : s ≠ 0 := by intro h; simp [h] at hs; linarith
  have hz (y : ℝ) : s - gammaLine y ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp [gammaLine] at hr
    linarith
  unfold rawRemainder Delta lineWeight
  rw [laplace_second_div_sq hη hs0]
  congr 1
  congr 1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro y
  simp only [laplace_second_div_sq hη (hz y)]

@[blueprint "varlamov-scaled-explicit-formula"
  (title := "Varlamov, Lemma 6.1: explicit formula at one shift")
  (statement := /-- Under the published Kadiri formula, the actual scaled
  kernel satisfies the explicit formula for every $\Re s>1/2$. Its raw
  second-derivative remainder is proved equal to the defined Delta, and
  the real zero sum converges with PNT+ multiplicities. -/)
  (uses := ["varlamov-test-kernel-admissible", "varlamov-exact-transform"])]
theorem scaled_explicit_formula (hK2 : KadiriExplicitInput) {η : ℝ} {s : ℂ}
    (hη : 0 < η) (hs : (1 / 2 : ℝ) < s.re) :
    Summable (fun ρ : riemannZeta.zeroes_rect (Set.Ioo 0 1) Set.univ =>
      (W ((s - (ρ : ℂ)) / (η : ℂ))).re * (riemannZeta.order (ρ : ℂ) : ℝ)) ∧
    primeSum (smoothKernel η) s = 10 * η * gammaTerm s + (W ((s - 1) / (η : ℂ))).re -
      riemannZeta.zeroes_sum (Set.Ioo 0 1) Set.univ (fun ρ => (W ((s - ρ) / (η : ℂ))).re) +
      (Delta η s).re := by
  have h := hK2 (d / η + 1) (smoothKernel η) (smooth_admissible hη) s hs
  simpa only [laplace_smoothKernel hη, smoothKernel_zero hη, rawRemainder_smooth hη hs] using h

#print axioms scaled_explicit_formula
end Kernel
end Varlamov
