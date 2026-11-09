import PrimeNumberTheoremAnd.IEANTN.Varlamov.HalfPlaneBounds
import PrimeNumberTheoremAnd.ResidueCalcOnRectangles

namespace Varlamov
open Real Complex MeasureTheory Filter Topology Set
open scoped Interval

noncomputable def cauchyResolvent (f : ℂ → ℂ) (p z : ℂ) : ℂ := f z / (z - p)

def upperLeft (R : ℝ) : ℂ := ⟨-R,0⟩
def upperRight (R : ℝ) : ℂ := ⟨R,R⟩

lemma upper_rectangle_subset {R : ℝ} (hR : 0 ≤ R) :
    Rectangle (upperLeft R) (upperRight R) ⊆ {z : ℂ | 0 ≤ z.im} := by
  intro z hz
  have hc := (mem_Rect (z := upperLeft R) (w := upperRight R)
    (show (upperLeft R).re ≤ (upperRight R).re by dsimp [upperLeft,upperRight]; linarith)
    hR z).mp hz
  exact hc.2.2.1

lemma upper_rectangle_cauchy {f : ℂ → ℂ} (hf : UpperCauchyAdmissible f)
    {p : ℂ} (hp : p.im ≠ 0) {R : ℝ} (hR : ‖p‖ + 1 ≤ R) :
    RectangleIntegral' (cauchyResolvent f p) (upperLeft R) (upperRight R) =
      if 0 < p.im then f p else 0 := by
  have hRp : ‖p‖ < R := by linarith
  have hR0 : 0 < R := (norm_nonneg p).trans_lt hRp
  have hre : (upperLeft R).re ≤ (upperRight R).re := by dsimp [upperLeft,upperRight]; linarith
  have him : (upperLeft R).im ≤ (upperRight R).im := hR0.le
  have hsub := upper_rectangle_subset hR0.le
  have hfrect : HolomorphicOn f (Rectangle (upperLeft R) (upperRight R)) := by
    intro z hz
    exact (hf.analytic z (hsub hz)).differentiableAt.differentiableWithinAt
  by_cases hpos : 0 < p.im
  · rw [ite_eq_left hpos]
    have hpRect : Rectangle (upperLeft R) (upperRight R) ∈ 𝓝 p := by
      rw [rectangle_mem_nhds_iff]
      have hpRe : |p.re| < R := (Complex.abs_re_le_norm p).trans_lt hRp
      have hpIm : p.im < R := (Complex.im_le_norm p).trans_lt hRp
      simp only [upperLeft,upperRight,mem_reProdIm]
      rw [uIoo_of_lt (show -R < R by linarith),uIoo_of_lt hR0]
      exact ⟨abs_lt.mp hpRe,⟨hpos,hpIm⟩⟩
    have hg : HolomorphicOn (dslope f p) (Rectangle (upperLeft R) (upperRight R)) :=
      (Complex.differentiableOn_dslope hpRect).mpr hfrect
    apply ResidueTheoremOnRectangleWithSimplePole hre him hpRect hg
    intro z hz
    have hne : z ≠ p := hz.2
    simp only [Pi.sub_apply, cauchyResolvent, dslope_of_ne f hne, slope_def_field]
    ring
  · rw [ite_eq_right hpos]
    have hpneg : p.im < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hp
    have hg : HolomorphicOn (cauchyResolvent f p) (Rectangle (upperLeft R) (upperRight R)) := by
      intro z hz
      have hne : z - p ≠ 0 := by
        intro he
        have hi := congrArg Complex.im he
        simp only [Complex.sub_im,Complex.zero_im] at hi
        have hz' := hsub hz
        change 0 ≤ z.im at hz'
        linarith
      exact ((hf.analytic z (hsub hz)).differentiableAt.div
        (by fun_prop : DifferentiableAt ℂ (fun z : ℂ => z - p) z) hne).differentiableWithinAt
    have hzero := hg.vanishesOnRectangle (show Rectangle (upperLeft R) (upperRight R) ⊆
      Rectangle (upperLeft R) (upperRight R) from subset_rfl)
    simp only [RectangleIntegral',hzero,smul_zero]

lemma upper_top_bound {f : ℂ → ℂ} {M R : ℝ} {p : ℂ}
    (hdec : ∀ z : ℂ, 0 ≤ z.im → ‖z‖ ^ 2 * ‖f z‖ < M)
    (hR : 0 < R) (hRp : 2 * ‖p‖ ≤ R) :
    ‖HIntegral (cauchyResolvent f p) (-R) R R‖ ≤ 4 * M / R ^ 2 := by
  have hb : ∀ x : ℝ, x ∈ Ι (-R) R →
      ‖cauchyResolvent f p ((x : ℂ) + (R : ℂ) * Complex.I)‖ ≤ 2 * M / R ^ 3 := by
    intro x _
    apply far_resolvent_bound hdec hR hRp
    · simpa using hR.le
    · have h := Complex.im_le_norm ((x : ℂ) + (R : ℂ) * Complex.I)
      simpa using h
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hb
  change ‖∫ x in (-R)..R, cauchyResolvent f p ((x : ℂ) + (R : ℂ) * Complex.I)‖ ≤ _
  apply h.trans_eq
  rw [abs_of_pos (by linarith : 0 < R - -R)]
  field_simp
  <;> ring

lemma upper_vertical_bound {f : ℂ → ℂ} {M R x : ℝ} {p : ℂ}
    (hdec : ∀ z : ℂ, 0 ≤ z.im → ‖z‖ ^ 2 * ‖f z‖ < M)
    (hR : 0 < R) (hRp : 2 * ‖p‖ ≤ R) (hx : R ≤ |x|) :
    ‖VIntegral (cauchyResolvent f p) x 0 R‖ ≤ 2 * M / R ^ 2 := by
  have hb : ∀ y : ℝ, y ∈ Ι (0 : ℝ) R →
      ‖cauchyResolvent f p ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤ 2 * M / R ^ 3 := by
    intro y hy
    rw [uIoc_of_le hR.le] at hy
    apply far_resolvent_bound hdec hR hRp
    · simpa using hy.1.le
    · have h := Complex.abs_re_le_norm ((x : ℂ) + (y : ℂ) * Complex.I)
      exact hx.trans (by simpa using h)
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hb
  simp only [VIntegral,norm_smul,Complex.norm_I,one_mul]
  apply h.trans_eq
  rw [sub_zero,abs_of_pos hR]
  field_simp
  <;> ring

lemma tendsto_zero_of_square_bound {F : ℝ → ℂ} {C : ℝ}
    (h : ∀ᶠ R : ℝ in atTop, ‖F R‖ ≤ C / R ^ 2) :
    Tendsto F atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero' (Filter.Eventually.of_forall (fun R => norm_nonneg (F R))) h
    (tendsto_const_div_square C)

lemma upper_rectangle_tendsto {f : ℂ → ℂ} (hf : UpperCauchyAdmissible f)
    {p : ℂ} (hp : p.im ≠ 0) :
    Tendsto (fun R : ℝ => RectangleIntegral (cauchyResolvent f p) (upperLeft R) (upperRight R))
      atTop (𝓝 (∫ t : ℝ, f (t : ℂ) / ((t : ℂ) - p))) := by
  obtain ⟨M,hM,hdec⟩ := hf.decay
  have ht : Tendsto (fun R : ℝ => HIntegral (cauchyResolvent f p) (-R) R R) atTop (𝓝 0) := by
    apply tendsto_zero_of_square_bound (C := 4 * M)
    filter_upwards [eventually_ge_atTop (1 + 2 * ‖p‖)] with R hR
    have hR0 : 0 < R := by have := norm_nonneg p; linarith
    exact upper_top_bound hdec hR0 (by linarith)
  have hr : Tendsto (fun R : ℝ => VIntegral (cauchyResolvent f p) R 0 R) atTop (𝓝 0) := by
    apply tendsto_zero_of_square_bound (C := 2 * M)
    filter_upwards [eventually_ge_atTop (1 + 2 * ‖p‖)] with R hR
    have hR0 : 0 < R := by have := norm_nonneg p; linarith
    exact upper_vertical_bound hdec hR0 (by linarith) (by simp [abs_of_pos hR0])
  have hl : Tendsto (fun R : ℝ => VIntegral (cauchyResolvent f p) (-R) 0 R) atTop (𝓝 0) := by
    apply tendsto_zero_of_square_bound (C := 2 * M)
    filter_upwards [eventually_ge_atTop (1 + 2 * ‖p‖)] with R hR
    have hR0 : 0 < R := by have := norm_nonneg p; linarith
    exact upper_vertical_bound hdec hR0 (by linarith) (by simp [abs_of_pos hR0])
  have hb := intervalIntegral_tendsto_integral (hf.cauchy_line_integrable hp)
    tendsto_neg_atTop_atBot tendsto_id
  have hb' : Tendsto (fun R : ℝ => HIntegral (cauchyResolvent f p) (-R) R 0) atTop
      (𝓝 (∫ t : ℝ, f (t : ℂ) / ((t : ℂ) - p))) := by
    simpa only [HIntegral,cauchyResolvent,Complex.ofReal_zero,zero_mul,add_zero,id_eq] using hb
  simpa only [RectangleIntegral,upperLeft,upperRight,sub_zero,add_zero] using
    ((hb'.sub ht).add hr).sub hl

/-- The classical Cauchy projection is derived from the already proved
rectangle residue theorem and the quadratic-decay hypotheses. -/
@[blueprint "varlamov-half-plane-cauchy"
  (title := "Classical half-plane Cauchy projection, proved in Lean")
  (statement := /-- A function analytic near the closed upper half-plane
  with quadratic decay has an integrable Cauchy kernel on the real line.
  Its normalized integral is the value at an upper point and zero at a lower
  point. The rectangle residue theorem and the vanishing of the three remote
  sides prove the formula without a separate Cauchy input. -/)
  (uses := ["ResidueTheoremOnRectangleWithSimplePole"])]
theorem halfPlaneCauchyInput_proved : HalfPlaneCauchyInput := by
  intro f hf p hp
  refine ⟨hf.cauchy_line_integrable hp, ?_⟩
  have hlim := (upper_rectangle_tendsto hf hp).const_smul (1 / (2 * (Real.pi : ℂ) * Complex.I))
  have heq : ∀ᶠ R : ℝ in atTop,
      RectangleIntegral' (cauchyResolvent f p) (upperLeft R) (upperRight R) =
        if 0 < p.im then f p else 0 := by
    filter_upwards [eventually_ge_atTop (‖p‖ + 1)] with R hR
    exact upper_rectangle_cauchy hf hp hR
  have hc : Tendsto (fun R : ℝ => RectangleIntegral' (cauchyResolvent f p) (upperLeft R) (upperRight R))
      atTop (𝓝 (if 0 < p.im then f p else 0)) :=
    tendsto_const_nhds.congr' (Filter.EventuallyEq.symm heq)
  have hresult := tendsto_nhds_unique hlim hc
  simpa only [smul_eq_mul] using hresult

#print axioms halfPlaneCauchyInput_proved
end Varlamov
