import PrimeNumberTheoremAnd.IEANTN.Varlamov.CauchyProjection

namespace Varlamov.Kernel
open Real MeasureTheory
open scoped BigOperators

noncomputable def gammaLine (y : ℝ) : ℂ := ((1 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I
noncomputable def lineWeight (η : ℝ) (s : ℂ) (y : ℝ) : ℂ := W0 ((s - gammaLine y) / (η : ℂ))
noncomputable def lineNorm : ℂ := 1 / (2 * (Real.pi : ℂ))
noncomputable def gammaRational (n : ℕ) (z : ℂ) : ℂ :=
  ((n : ℂ) + 1)⁻¹ - (z + 2 * (n : ℂ))⁻¹ - (1 - z + 2 * (n : ℂ))⁻¹
noncomputable def psiPartial : ℕ → ℂ → ℂ
  | 0, _ => -(Real.eulerMascheroniConstant : ℂ)
  | n + 1, z => psiPartial n z + gammaRational n z
noncomputable def zeroSample (η : ℝ) (s : ℂ) (n : ℕ) : ℂ := W0 ((s + 2 * (n : ℂ)) / (η : ℂ))

lemma gamma_single_projection (hC : HalfPlaneCauchyInput) {η : ℝ} {s : ℂ}
    (hη : 0 < η) (hs : (1 / 2 : ℝ) < s.re) (n : ℕ) :
    Integrable (fun y : ℝ => lineWeight η s y * gammaRational n (gammaLine y)) ∧
      lineNorm * (∫ y : ℝ, lineWeight η s y * gammaRational n (gammaLine y)) = -zeroSample η s n := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  let p : ℂ := -2 * (n : ℂ)
  let q : ℂ := 1 + 2 * (n : ℂ)
  have hpleft : p.re < (1 / 2 : ℝ) := by simp only [p, neg_mul, Complex.neg_re,
    Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, Complex.natCast_re,
    Complex.natCast_im, mul_zero, sub_zero]; linarith
  have hqright : (1 / 2 : ℝ) < q.re := by simp only [q, Complex.add_re, Complex.one_re,
    Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, Complex.natCast_re,
    Complex.natCast_im, mul_zero, sub_zero]; linarith
  have hbase := left_line_W0_zero hC hη hs
  have hleft := left_cauchy_W0 hC hη hs (p := p) (ne_of_lt hpleft)
  have hright := left_cauchy_W0 hC hη hs (p := q) (ne_of_gt hqright)
  have hl : Integrable (fun y : ℝ => lineWeight η s y / (gammaLine y + 2 * (n : ℂ))) := by
    simpa only [lineWeight, gammaLine, p, sub_neg_eq_add, neg_mul] using hleft.1
  have hleq : lineNorm * (∫ y : ℝ, lineWeight η s y / (gammaLine y + 2 * (n : ℂ))) = zeroSample η s n := by
    have h' := hleft.2
    rw [ite_eq_left hpleft] at h'
    simpa only [lineNorm, lineWeight, gammaLine, p, sub_neg_eq_add, neg_mul, zeroSample] using h' 
  have hrpoint (y : ℝ) : lineWeight η s y / (1 - gammaLine y + 2 * (n : ℂ)) =
      - (lineWeight η s y / (gammaLine y - q)) := by
    rw [show 1 - gammaLine y + 2 * (n : ℂ) = -(gammaLine y - q) from by dsimp [q]; ring, div_neg]
  have hr : Integrable (fun y : ℝ => lineWeight η s y / (1 - gammaLine y + 2 * (n : ℂ))) := by
    have h' : Integrable (fun y : ℝ => -(lineWeight η s y / (gammaLine y - q))) := by
      exact hright.1.neg.congr (Filter.Eventually.of_forall (fun y => by rfl))
    exact h'.congr (Filter.Eventually.of_forall (fun y => (hrpoint y).symm))
  have hreq : lineNorm * (∫ y : ℝ, lineWeight η s y / (1 - gammaLine y + 2 * (n : ℂ))) = 0 := by
    have h' : lineNorm * (∫ y : ℝ, lineWeight η s y / (gammaLine y - q)) = 0 := by
      simpa only [lineNorm, lineWeight, gammaLine, ite_eq_right (not_lt_of_ge hqright.le)] using hright.2
    rw [integral_congr_ae (Filter.Eventually.of_forall hrpoint), integral_neg]
    simpa only [mul_neg, h', neg_zero]
  have hb : Integrable (lineWeight η s) := by
    convert hbase.1 using 1
    funext y
    rfl
  have hb0 : lineNorm * (∫ y : ℝ, lineWeight η s y) = 0 := by
    simpa only [lineNorm, lineWeight, gammaLine] using hbase.2
  let c : ℂ := ((n : ℂ) + 1)⁻¹
  have hc : Integrable (fun y : ℝ => lineWeight η s y * c) := hb.mul_const c
  have hceq : lineNorm * (∫ y : ℝ, lineWeight η s y * c) = 0 := by
    rw [integral_mul_const, ← mul_assoc, hb0, zero_mul]
  have heq (y : ℝ) : lineWeight η s y * gammaRational n (gammaLine y) =
      (lineWeight η s y * c - lineWeight η s y / (gammaLine y + 2 * (n : ℂ))) -
        lineWeight η s y / (1 - gammaLine y + 2 * (n : ℂ)) := by
    dsimp [c, gammaRational]
    ring
  have hi : Integrable (fun y : ℝ => lineWeight η s y * gammaRational n (gammaLine y)) :=
    ((hc.sub hl).sub hr).congr (Filter.Eventually.of_forall (fun y => (heq y).symm))
  refine ⟨hi, ?_⟩
  have houter := integral_sub (hc.sub hl) hr
  have hinner := integral_sub hc hl
  simp only [Pi.sub_apply] at houter hinner
  rw [integral_congr_ae (Filter.Eventually.of_forall heq), houter, hinner,
    mul_sub, mul_sub, hceq, hleq, hreq]
  ring

/-- The finite version of Proposition 6.3, with every pole projected exactly. -/
theorem gamma_partial_projection (hC : HalfPlaneCauchyInput) {η : ℝ} {s : ℂ}
    (hη : 0 < η) (hs : (1 / 2 : ℝ) < s.re) (N : ℕ) :
    Integrable (fun y : ℝ => lineWeight η s y * psiPartial N (gammaLine y)) ∧
      lineNorm * (∫ y : ℝ, lineWeight η s y * psiPartial N (gammaLine y)) =
        - (∑ n ∈ Finset.range N, zeroSample η s n) := by
  induction N with
  | zero =>
      have hb := left_line_W0_zero hC hη hs
      have hi : Integrable (lineWeight η s) := by
        convert hb.1 using 1
        funext y
        rfl
      have he : lineNorm * (∫ y : ℝ, lineWeight η s y) = 0 := by
        simpa only [lineNorm, lineWeight, gammaLine] using hb.2
      constructor
      · exact hi.mul_const _
      · simp only [psiPartial, integral_mul_const, ← mul_assoc, he, zero_mul, Finset.sum_range_zero, neg_zero]
  | succ N ih =>
      have hn := gamma_single_projection hC hη hs N
      have heq (y : ℝ) : lineWeight η s y * psiPartial (N + 1) (gammaLine y) =
          lineWeight η s y * psiPartial N (gammaLine y) +
            lineWeight η s y * gammaRational N (gammaLine y) := by rw [psiPartial, mul_add]
      constructor
      · exact (ih.1.add hn.1).congr (Filter.Eventually.of_forall (fun y => (heq y).symm))
      · rw [integral_congr_ae (Filter.Eventually.of_forall heq), integral_add ih.1 hn.1,
          mul_add, ih.2, hn.2, Finset.sum_range_succ]
        ring

#print axioms gamma_partial_projection

end Varlamov.Kernel
