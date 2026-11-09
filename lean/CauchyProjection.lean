import PrimeNumberTheoremAnd.IEANTN.Varlamov.CauchyInput

namespace Varlamov.Kernel
open Real MeasureTheory

/-- Apply the explicitly named upper-half-plane Cauchy input after rotation.
All its analytic and decay conditions are proved for the actual W0 weight. -/
theorem left_cauchy_affine (hC : HalfPlaneCauchyInput) {η a : ℝ} {s p : ℂ}
    (hη : 0 < η) (has : a < s.re) (A B : ℂ) (hp : p.re ≠ a) :
    Integrable (fun t : ℝ => affineWeight η s A B ((a : ℂ) + (t : ℂ) * Complex.I) /
      ((a : ℂ) + (t : ℂ) * Complex.I - p)) ∧
    (1 / (2 * (Real.pi : ℂ))) * (∫ t : ℝ,
      affineWeight η s A B ((a : ℂ) + (t : ℂ) * Complex.I) /
        ((a : ℂ) + (t : ℂ) * Complex.I - p)) =
      if p.re < a then affineWeight η s A B p else 0 := by
  let wp : ℂ := (p - (a : ℂ)) / Complex.I
  have hwpim : wp.im = a - p.re := by
    norm_num [wp, Complex.div_im, Complex.normSq_apply, Complex.I_re, Complex.I_im,
      Complex.sub_re, Complex.ofReal_re]
    
  have hwp : wp.im ≠ 0 := by rw [hwpim]; exact sub_ne_zero.mpr hp.symm
  have himage : (a : ℂ) + wp * Complex.I = p := by
    dsimp [wp]
    field_simp
    ring
  have h := hC (rotatedWeight η a s A B) (rotatedWeight_admissible hη has A B) wp hwp
  let K : ℝ → ℂ := fun t => affineWeight η s A B ((a : ℂ) + (t : ℂ) * Complex.I) /
    ((a : ℂ) + (t : ℂ) * Complex.I - p)
  have hpoint (t : ℝ) : rotatedWeight η a s A B (t : ℂ) / ((t : ℂ) - wp) = Complex.I * K t := by
    have ht : (t : ℂ) - wp ≠ 0 := by
      intro he
      have hi := congrArg Complex.im he
      simp only [Complex.sub_im, Complex.ofReal_im, Complex.zero_im] at hi
      exact hwp (by linarith)
    have he : (a : ℂ) + (t : ℂ) * Complex.I - p = Complex.I * ((t : ℂ) - wp) := by
      rw [← himage]
      ring
    dsimp [K, rotatedWeight]
    rw [he]
    field_simp
    
  have hIK : Integrable (fun t : ℝ => Complex.I * K t) := by
    simpa only [hpoint] using h.1
  have hK : Integrable K := by
    have h' := hIK.const_mul (-Complex.I)
    simpa only [← mul_assoc, neg_mul, Complex.I_mul_I, neg_neg, one_mul] using h'
  have hf := h.2
  simp_rw [hpoint] at hf
  rw [MeasureTheory.integral_const_mul] at hf
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hpref : (1 / (2 * (Real.pi : ℂ) * Complex.I)) * Complex.I = 1 / (2 * (Real.pi : ℂ)) := by
    field_simp
  rw [← mul_assoc, hpref] at hf
  have hside : (0 < wp.im) = (p.re < a) := propext (by rw [hwpim]; exact sub_pos)
  simp only [hside] at hf
  simp only [rotatedWeight, himage] at hf
  exact ⟨hK, hf⟩

/-- Pure Cauchy projection of the remainder weight at either side of the line. -/
theorem left_cauchy_W0 (hC : HalfPlaneCauchyInput) {η a : ℝ} {s p : ℂ}
    (hη : 0 < η) (has : a < s.re) (hp : p.re ≠ a) :
    Integrable (fun t : ℝ => W0 ((s - ((a : ℂ) + (t : ℂ) * Complex.I)) / (η : ℂ)) /
      ((a : ℂ) + (t : ℂ) * Complex.I - p)) ∧
    (1 / (2 * (Real.pi : ℂ))) * (∫ t : ℝ,
      W0 ((s - ((a : ℂ) + (t : ℂ) * Complex.I)) / (η : ℂ)) /
      ((a : ℂ) + (t : ℂ) * Complex.I - p)) =
      if p.re < a then W0 ((s - p) / (η : ℂ)) else 0 := by
  simpa only [affineWeight, zero_mul, add_zero, one_mul] using
    left_cauchy_affine hC hη has 1 0 hp

/-- The constant term in each finite digamma approximation integrates to zero. -/
theorem left_line_W0_zero (hC : HalfPlaneCauchyInput) {η a : ℝ} {s : ℂ}
    (hη : 0 < η) (has : a < s.re) :
    Integrable (fun t : ℝ => W0 ((s - ((a : ℂ) + (t : ℂ) * Complex.I)) / (η : ℂ))) ∧
    (1 / (2 * (Real.pi : ℂ))) * (∫ t : ℝ,
      W0 ((s - ((a : ℂ) + (t : ℂ) * Complex.I)) / (η : ℂ))) = 0 := by
  let q : ℂ := (((a + 1 : ℝ) : ℂ))
  have hq : q.re ≠ a := by simp only [q, Complex.ofReal_re]; linarith
  have h := left_cauchy_affine hC hη has (-q) 1 (p := q) hq
  have hpoint (t : ℝ) : affineWeight η s (-q) 1 ((a : ℂ) + (t : ℂ) * Complex.I) /
      ((a : ℂ) + (t : ℂ) * Complex.I - q) =
      W0 ((s - ((a : ℂ) + (t : ℂ) * Complex.I)) / (η : ℂ)) := by
    have hden : (a : ℂ) + (t : ℂ) * Complex.I - q ≠ 0 := by
      intro he
      have hr := congrArg Complex.re he
      simp [q] at hr
    dsimp [affineWeight]
    field_simp
    ring
  have hi : Integrable (fun t : ℝ => W0 ((s - ((a : ℂ) + (t : ℂ) * Complex.I)) / (η : ℂ))) :=
    h.1.congr (Filter.Eventually.of_forall hpoint)
  have hf := h.2
  simp_rw [hpoint] at hf
  rw [ite_eq_right (show ¬ q.re < a by simp only [q, Complex.ofReal_re]; linarith)] at hf
  exact ⟨hi, hf⟩

#print axioms left_cauchy_W0
#print axioms left_line_W0_zero

end Varlamov.Kernel
