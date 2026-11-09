import PrimeNumberTheoremAnd.IEANTN.Varlamov.TransformAnalytic
import PrimeNumberTheoremAnd.IEANTN.Varlamov.TransformDecay
import Mathlib.Tactic.GCongr

/-!
# Explicit classical input for the remainder identity

The half-plane Cauchy projection is an ordinary theorem parameter. Sources:
* Brown--Churchill, Complex Variables and Applications, 8th ed. (2009),
  section 126, pp. 440--441, equation (3) and the paragraph immediately after it:
  https://www.math.utoronto.ca/~jeffrey/matd34/churchillbrown.pdf#page=453
* Katsnelson--Weiss, A Counterexample in Hardy Spaces with an Application to
  Systems Theory, Z. Anal. Anwend. 14 (1995), 705--730, p.706, (1.3):
  https://ems.press/content/serial-article-files/34831

The following statement uses the power-2 specialization of the first source.
The second source records the broader Hardy-space representation. The decay
and analyticity conditions for our actual transform are proved below in Lean.
-/

namespace Varlamov
open Real MeasureTheory

structure UpperCauchyAdmissible (f : ℂ → ℂ) : Prop where
  analytic : AnalyticOnNhd ℂ f {z : ℂ | 0 ≤ z.im}
  decay : ∃ M : ℝ, 0 < M ∧ ∀ z : ℂ, 0 ≤ z.im → ‖z‖ ^ 2 * ‖f z‖ < M

def HalfPlaneCauchyInput : Prop :=
  ∀ f : ℂ → ℂ, UpperCauchyAdmissible f → ∀ p : ℂ, p.im ≠ 0 →
    Integrable (fun t : ℝ => f (t : ℂ) / ((t : ℂ) - p)) ∧
    (1 / (2 * (Real.pi : ℂ) * Complex.I)) * (∫ t : ℝ, f (t : ℂ) / ((t : ℂ) - p)) =
      if 0 < p.im then f p else 0

namespace Kernel
noncomputable def W0 (z : ℂ) : ℂ := W z - 10 / z
noncomputable def affineWeight (η : ℝ) (s A B z : ℂ) : ℂ :=
  (A + B * z) * W0 ((s - z) / (η : ℂ))
noncomputable def rotatedWeight (η a : ℝ) (s A B w : ℂ) : ℂ :=
  affineWeight η s A B ((a : ℂ) + w * Complex.I)

/-- The actual remainder weight, and its product with any affine factor,
satisfy all hypotheses of the published half-plane Cauchy formula. -/
theorem rotatedWeight_admissible {η a : ℝ} {s : ℂ}
    (hη : 0 < η) (has : a < s.re) (A B : ℂ) :
    UpperCauchyAdmissible (rotatedWeight η a s A B) := by
  let δ : ℝ := s.re - a
  let ν : ℝ := δ / η
  have hδ : 0 < δ := sub_pos.mpr has
  have hν : 0 < ν := div_pos hδ hη
  let φ : ℂ → ℂ := fun w => (s - ((a : ℂ) + w * Complex.I)) / (η : ℂ)
  constructor
  · intro w hw
    change 0 ≤ w.im at hw
    have hφpos : 0 < (φ w).re := by
      simp only [φ, Complex.div_ofReal_re, Complex.sub_re, Complex.add_re,
        Complex.ofReal_re, Complex.mul_I_re]
      exact div_pos (by linarith) hη
    have hφne : φ w ≠ 0 := by
      intro h
      have hr := congrArg Complex.re h
      simp only [Complex.zero_re] at hr
      exact (ne_of_gt hφpos) hr
    have hφ : AnalyticAt ℂ φ w := by dsimp [φ]; fun_prop
    have hW : AnalyticAt ℂ W (φ w) := differentiable_W.analyticAt (φ w)
    have hmain : AnalyticAt ℂ (fun w => (10 : ℂ) / φ w) w := analyticAt_const.div hφ hφne
    have hfactor : AnalyticAt ℂ (fun w => A + B * ((a : ℂ) + w * Complex.I)) w := by fun_prop
    change AnalyticAt ℂ (fun w => (A + B * ((a : ℂ) + w * Complex.I)) * (W (φ w) - 10 / φ w)) w
    exact hfactor.mul ((hW.comp hφ).sub hmain)
  · let P : ℝ := C ν * η ^ 3
    let k : ℝ := ‖s - (a : ℂ)‖
    let c : ℝ := ‖A + B * s‖
    let b : ℝ := ‖B‖
    have hP : 0 < P := mul_pos (C_pos hν) (pow_pos hη 3)
    have hk : 0 ≤ k := norm_nonneg _
    have hc : 0 ≤ c := norm_nonneg _
    have hb : 0 ≤ b := norm_nonneg _
    refine ⟨P * (k / δ + 1) ^ 2 * (c / δ + b) + 1, by positivity, ?_⟩
    intro w hw
    let Z : ℂ := (a : ℂ) + w * Complex.I
    let U : ℂ := s - Z
    let r : ℝ := ‖U‖
    have hUre : δ ≤ U.re := by
      simp only [U, Z, δ, Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_I_re]
      linarith
    have hδr : δ ≤ r := hUre.trans (Complex.re_le_norm U)
    have hr : 0 < r := hδ.trans_le hδr
    have hrne : r ≠ 0 := ne_of_gt hr
    have hη0 : η ≠ 0 := ne_of_gt hη
    have harg : ν ≤ (U / (η : ℂ)).re := by
      rw [Complex.div_ofReal_re]
      exact div_le_div_of_nonneg_right hUre hη.le
    have hV : ‖W0 (U / (η : ℂ))‖ ≤ P / r ^ 3 := by
      have h := W_right_bound hν harg
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hη] at h
      change ‖W (U / (η : ℂ)) - 10 / (U / (η : ℂ))‖ ≤ _
      convert h using 1
      dsimp [P, r]
      field_simp
      
    have hwNorm : ‖w‖ ≤ k + r := by
      calc
        ‖w‖ = ‖w * Complex.I‖ := by simp
        _ = ‖(s - (a : ℂ)) - U‖ := by congr 1; dsimp [U, Z]; ring
        _ ≤ k + r := norm_sub_le _ _
    have hlinear : ‖A + B * Z‖ ≤ c + b * r := by
      rw [show A + B * Z = (A + B * s) - B * U from by dsimp [U]; ring]
      calc
        _ ≤ c + ‖B * U‖ := norm_sub_le _ _
        _ = c + b * r := by rw [norm_mul]
    have hAffine : ‖rotatedWeight η a s A B w‖ ≤ (c + b * r) * P / r ^ 3 := by
      change ‖(A + B * Z) * W0 (U / (η : ℂ))‖ ≤ _
      rw [norm_mul]
      calc
        _ ≤ (c + b * r) * (P / r ^ 3) := mul_le_mul hlinear hV (norm_nonneg _) (by positivity)
        _ = _ := by ring
    have hsq : ‖w‖ ^ 2 ≤ (k + r) ^ 2 := by gcongr
    have hbound : ‖w‖ ^ 2 * ‖rotatedWeight η a s A B w‖ ≤ P * (k / δ + 1) ^ 2 * (c / δ + b) := by
      calc
        _ ≤ (k + r) ^ 2 * ((c + b * r) * P / r ^ 3) := mul_le_mul hsq hAffine (norm_nonneg _) (sq_nonneg _)
        _ = P * (k / r + 1) ^ 2 * (c / r + b) := by field_simp 
        _ ≤ _ := by gcongr
    exact hbound.trans_lt (by linarith)

#print axioms rotatedWeight_admissible

end Kernel
end Varlamov
