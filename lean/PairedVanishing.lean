import PrimeNumberTheoremAnd.IEANTN.Varlamov.PairedStrip

namespace Varlamov
open Real

/-- The strip minimum principle needs only vanishing at infinity, not a
positive leading coefficient on the horizontal sides. Apply the finite
rectangle theorem to F+epsilon/2 and let epsilon decrease to zero. -/
theorem paired_nonneg_of_boundary_and_vanishing {F : ℂ → ℂ}
    (hF : Differentiable ℂ F) (h : ℝ)
    (hvertical : ∀ z : ℂ, z.re = 0 ∨ z.re = h →
      0 ≤ (F z + F ((h : ℂ) - z)).re)
    (hvanish : ∀ ε : ℝ, 0 < ε → ∃ Y : ℝ, ∀ z : ℂ,
      z.re ∈ Set.Icc (0 : ℝ) h → Y ≤ |z.im| → ‖F z‖ ≤ ε)
    {z : ℂ} (hz : z.re ∈ Set.Icc (0 : ℝ) h) :
    0 ≤ (F z + F ((h : ℂ) - z)).re := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨Y, hY⟩ := hvanish (ε / 2) (by linarith)
  let Fε : ℂ → ℂ := fun w => F w + ((ε / 2 : ℝ) : ℂ)
  have hFε : Differentiable ℂ Fε := hF.add_const _
  have hv : ∀ w : ℂ, w.re = 0 ∨ w.re = h →
      0 ≤ (Fε w + Fε ((h : ℂ) - w)).re := by
    intro w hw
    have hh := hvertical w hw
    simp only [Fε, Complex.add_re, Complex.ofReal_re] at hh ⊢
    linarith
  have hf : ∃ Y₀ : ℝ, ∀ w : ℂ, w.re ∈ Set.Icc (0 : ℝ) h → Y₀ ≤ |w.im| →
      0 ≤ (Fε w + Fε ((h : ℂ) - w)).re := by
    refine ⟨Y, ?_⟩
    intro w hw hy
    have h1 := hY w hw hy
    have hwr : ((h : ℂ) - w).re ∈ Set.Icc (0 : ℝ) h := by
      simp only [Complex.sub_re, Complex.ofReal_re]
      constructor <;> linarith [hw.1, hw.2]
    have hwi : |((h : ℂ) - w).im| = |w.im| := by simp
    have h2 := hY ((h : ℂ) - w) hwr (by simpa [hwi] using hy)
    have hr1 := Complex.abs_re_le_norm (F w)
    have hr2 := Complex.abs_re_le_norm (F ((h : ℂ) - w))
    have hn1 := neg_abs_le (F w).re
    have hn2 := neg_abs_le (F ((h : ℂ) - w)).re
    simp only [Fε, Complex.add_re, Complex.ofReal_re]
    linarith
  have hh := paired_nonneg_of_boundary_and_far hFε h hv hf hz
  simp only [Fε, Complex.add_re, Complex.ofReal_re] at hh
  simp only [Complex.add_re]
  linarith

#print axioms paired_nonneg_of_boundary_and_vanishing

end Varlamov
