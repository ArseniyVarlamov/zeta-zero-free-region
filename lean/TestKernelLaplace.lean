import PrimeNumberTheoremAnd.IEANTN.Varlamov.TestKernel
import PrimeNumberTheoremAnd.IEANTN.Varlamov.TransformSupport

namespace Varlamov.Kernel
open Real MeasureTheory

noncomputable def laplace (f : ℝ → ℝ) (z : ℂ) : ℂ :=
  ∫ u in Set.Ioi (0 : ℝ), Complex.exp (-z * (u : ℂ)) * (f u : ℂ)

lemma laplace_eq_compact_interval {f : ℝ → ℝ} {D : ℝ} (hD : 0 ≤ D)
    (hs : Function.support f ⊆ Set.Icc (0 : ℝ) D) (z : ℂ) :
    laplace f z = ∫ u in (0 : ℝ)..D, Complex.exp (-z * (u : ℂ)) * (f u : ℂ) := by
  let ψ : ℝ → ℂ := fun u => Complex.exp (-z * (u : ℂ)) * (f u : ℂ)
  let χ : ℝ → ℂ := (Set.Ioi (0 : ℝ)).indicator ψ
  have hχ : Function.support χ ⊆ Set.Ioc (0 : ℝ) D := by
    intro u hu
    have hn : χ u ≠ 0 := hu
    have hu0 : 0 < u := by
      by_contra h
      exact hn (by simp [χ, h])
    have hf : f u ≠ 0 := by
      intro hf
      exact hn (by simp [χ, ψ, hf])
    exact ⟨hu0, (hs hf).2⟩
  unfold laplace
  change (∫ u in Set.Ioi (0 : ℝ), ψ u) = _
  rw [← MeasureTheory.integral_indicator measurableSet_Ioi]
  change (∫ u : ℝ, χ u) = _
  rw [← intervalIntegral.integral_eq_integral_of_support_subset hχ]
  apply intervalIntegral.integral_congr_Ioo_of_le hD
  intro u hu
  change (Set.Ioi (0 : ℝ)).indicator ψ u = ψ u
  exact Set.indicator_of_mem (show u ∈ Set.Ioi (0 : ℝ) from hu.1) ψ

/-- Exact scaling identity required in the application of K2. -/
theorem laplace_g {η : ℝ} (hη : 0 < η) (z : ℂ) : laplace (g η) z = W (z / (η : ℂ)) := by
  have hD : 0 < d / η := div_pos d_pos hη
  have hη0 : η ≠ 0 := ne_of_gt hη
  have hηC : (η : ℂ) ≠ 0 := by exact_mod_cast hη0
  let φ : ℝ → ℂ := fun v => Complex.exp (-(z / (η : ℂ)) * (v : ℂ)) * (w v : ℂ)
  have hpoint (u : ℝ) : φ (η * u) = Complex.exp (-z * (u : ℂ)) * (w (η * u) : ℂ) := by
    dsimp [φ]
    push_cast
    congr 2
    field_simp
    
  have hchange := intervalIntegral.smul_integral_comp_mul_left φ (a := 0) (b := d / η) η
  have hend : η * (d / η) = d := by field_simp
  simp only [mul_zero, hend, Complex.real_smul] at hchange
  simp_rw [hpoint] at hchange
  have hW : (∫ v in (0 : ℝ)..d, φ v) = W (z / (η : ℂ)) := by
    apply intervalIntegral.integral_congr
    intro v hv
    rw [Set.uIcc_of_le d_pos.le] at hv
    change Complex.exp (-(z / (η : ℂ)) * (v : ℂ)) * (w v : ℂ) =
      Complex.exp (-(z / (η : ℂ)) * (v : ℂ)) * (piece v : ℂ)
    rw [w_piece hv]
  calc
    laplace (g η) z = ∫ u in (0 : ℝ)..(d / η), Complex.exp (-z * (u : ℂ)) * (g η u : ℂ) :=
      laplace_eq_compact_interval hD.le (g_support hη) z
    _ = ∫ u in (0 : ℝ)..(d / η), (η : ℂ) *
        (Complex.exp (-z * (u : ℂ)) * (w (η * u) : ℂ)) := by
      apply intervalIntegral.integral_congr_Ioo_of_le hD.le
      intro u hu
      simp only [g, ite_eq_left hu.1.le, Complex.ofReal_mul]
      ring
    _ = (η : ℂ) * ∫ u in (0 : ℝ)..(d / η),
        Complex.exp (-z * (u : ℂ)) * (w (η * u) : ℂ) := intervalIntegral.integral_const_mul _ _
    _ = W (z / (η : ℂ)) := hchange.trans hW

#print axioms laplace_g

end Varlamov.Kernel
