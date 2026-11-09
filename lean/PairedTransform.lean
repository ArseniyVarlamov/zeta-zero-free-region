import PrimeNumberTheoremAnd.IEANTN.Varlamov.MultiplierData
import PrimeNumberTheoremAnd.IEANTN.Varlamov.TransformAnalytic
import PrimeNumberTheoremAnd.IEANTN.Varlamov.TransformDecay

namespace Varlamov
open Real
open scoped BigOperators ComplexConjugate

noncomputable def F (j : Fin 7) (h η : ℝ) (z : ℂ) : ℂ :=
  ∑ m ∈ Finset.range (Multiplier.length j), (Multiplier.coefficient j m : ℂ) *
    Kernel.W ((z + ((h * (m : ℝ) : ℝ) : ℂ)) / (η : ℂ))

noncomputable def Pi (j : Fin 7) (h η : ℝ) (z : ℂ) : ℝ :=
  (F j h η z).re + (F j h η ((h : ℂ) - conj z)).re

lemma F_differentiable (j : Fin 7) (h η : ℝ) : Differentiable ℂ (F j h η) := by
  unfold F
  apply Differentiable.fun_sum
  intro m _
  exact ((Kernel.differentiable_W.comp
    ((differentiable_id.add_const _).div_const _)).const_mul _)

lemma F_conj (j : Fin 7) (h η : ℝ) (z : ℂ) : F j h η (conj z) = conj (F j h η z) := by
  have he (m : ℕ) : (conj z + ((h * (m : ℝ) : ℝ) : ℂ)) / (η : ℂ) =
      conj ((z + ((h * (m : ℝ) : ℝ) : ℂ)) / (η : ℂ)) := by simp
  simp only [F, map_sum, map_mul, Complex.conj_ofReal]
  apply Finset.sum_congr rfl
  intro m _
  rw [he, Kernel.W_conj]

lemma Pi_analytic (j : Fin 7) (h η : ℝ) (z : ℂ) :
    Pi j h η z = (F j h η z + F j h η ((h : ℂ) - z)).re := by
  have he : (h : ℂ) - conj z = conj ((h : ℂ) - z) := by simp
  simp only [Pi, he, F_conj, Complex.conj_re, Complex.add_re]

lemma Pi_reflection (j : Fin 7) (h η : ℝ) (z : ℂ) :
    Pi j h η ((h : ℂ) - conj z) = Pi j h η z := by
  have he : (h : ℂ) - conj ((h : ℂ) - conj z) = z := by simp
  simp only [Pi, he]
  ring

lemma F_norm_large_im (j : Fin 7) {h η : ℝ} (hh : 0 ≤ h) (hη : 0 < η)
    {z : ℂ} (hx : 0 ≤ z.re) (hy : η ≤ |z.im|) :
    ‖F j h η z‖ ≤ Multiplier.coeffNorm j * (10 + Kernel.Cminus) * η / |z.im| := by
  have hy0 : 0 < |z.im| := hη.trans_le hy
  have hW (m : ℕ) :
      ‖Kernel.W ((z + ((h * (m : ℝ) : ℝ) : ℂ)) / (η : ℂ))‖ ≤
        (10 + Kernel.Cminus) * η / |z.im| := by
    let ξ : ℂ := (z + ((h * (m : ℝ) : ℝ) : ℂ)) / (η : ℂ)
    have hxr : 0 ≤ ξ.re := by
      simp only [ξ, Complex.div_ofReal_re, Complex.add_re, Complex.ofReal_re]
      exact div_nonneg (add_nonneg hx (mul_nonneg hh (Nat.cast_nonneg m))) hη.le
    have hxi : |ξ.im| = |z.im| / η := by
      simp [ξ, abs_div, abs_of_pos hη]
    have hxi1 : 1 ≤ |ξ.im| := by rw [hxi]; exact (le_div_iff₀ hη).mpr (by simpa using hy)
    have hb := Kernel.W_norm_large_im hxr hxi1
    rw [hxi, div_div_eq_mul_div] at hb
    exact hb
  unfold F
  calc
    _ ≤ ∑ m ∈ Finset.range (Multiplier.length j),
        ‖(Multiplier.coefficient j m : ℂ) *
          Kernel.W ((z + ((h * (m : ℝ) : ℝ) : ℂ)) / (η : ℂ))‖ := norm_sum_le _ _
    _ ≤ ∑ m ∈ Finset.range (Multiplier.length j),
        |Multiplier.coefficient j m| * ((10 + Kernel.Cminus) * η / |z.im|) := by
      apply Finset.sum_le_sum
      intro m _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hW m) (abs_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; unfold Multiplier.coeffNorm; ring

lemma F_vanishes_on_strip (j : Fin 7) {h η : ℝ} (hh : 0 ≤ h) (hη : 0 < η) :
    ∀ ε : ℝ, 0 < ε → ∃ Y : ℝ, ∀ z : ℂ,
      z.re ∈ Set.Icc (0 : ℝ) h → Y ≤ |z.im| → ‖F j h η z‖ ≤ ε := by
  intro ε hε
  let S : ℝ := Multiplier.coeffNorm j * (10 + Kernel.Cminus) * η
  have hS : 0 ≤ S := by
    dsimp [S]
    exact mul_nonneg (mul_nonneg (Multiplier.coeffNorm_nonneg j)
      (by linarith [Kernel.Cminus_pos])) hη.le
  refine ⟨η + 1 + S / ε, ?_⟩
  intro z hz hy
  have hyη : η ≤ |z.im| := by linarith [div_nonneg hS hε.le]
  have hy0 : 0 < |z.im| := hη.trans_le hyη
  have hs : S / ε ≤ |z.im| := by linarith
  have hs' : S ≤ ε * |z.im| := by
    have h' := (div_le_iff₀ hε).mp hs
    nlinarith
  exact (F_norm_large_im j hh hη hz.1 hyη).trans ((div_le_iff₀ hy0).mpr hs')

#print axioms F_differentiable
#print axioms F_vanishes_on_strip

end Varlamov
