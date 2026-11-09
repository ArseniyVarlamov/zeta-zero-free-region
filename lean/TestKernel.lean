import PrimeNumberTheoremAnd.IEANTN.Varlamov.KernelSmooth

namespace Varlamov.Kernel
open Real Topology

/-- The one-sided rescaled kernel to which Kadiri's formula is applied. -/
noncomputable def g (η u : ℝ) : ℝ := if 0 ≤ u then η * w (η * u) else 0

lemma g_nonneg {η : ℝ} (hη : 0 ≤ η) (u : ℝ) : 0 ≤ g η u := by
  unfold g
  split_ifs
  · exact mul_nonneg hη (w_nonneg _)
  · exact le_rfl
lemma g_zero (η : ℝ) : g η 0 = 10 * η := by simp [g, w_zero]; ring

lemma g_zero_of_gt {η u : ℝ} (hη : 0 < η) (hu : d / η < u) : g η u = 0 := by
  have hu0 : 0 < u := (div_pos d_pos hη).trans hu
  have hηu : d < η * u := by
    have h := (div_lt_iff₀ hη).mp hu
    nlinarith
  have hw := w_vanishes (u := η * u) (by rw [abs_of_pos (mul_pos hη hu0)]; exact hηu.le)
  simp [g, hu0.le, hw]

lemma g_support {η : ℝ} (hη : 0 < η) : Function.support (g η) ⊆ Set.Icc (0 : ℝ) (d / η) := by
  intro u hu
  have hn : g η u ≠ 0 := hu
  constructor
  · by_contra h
    exact hn (by simp [g, h])
  · by_contra h
    exact hn (g_zero_of_gt hη (lt_of_not_ge h))

lemma g_tsupport {η : ℝ} (hη : 0 < η) : tsupport (g η) ⊆ Set.Icc (0 : ℝ) (d / η) := by
  change closure (Function.support (g η)) ⊆ Set.Icc (0 : ℝ) (d / η)
  exact closure_minimal (g_support hη) isClosed_Icc

lemma g_eq_smooth {η u : ℝ} (hη : 0 < η) (hu : 0 ≤ u) :
    g η u = η * cut piece (η * u) := by
  simp only [g, ite_eq_left hu]
  rw [w_eq_cut_nonneg (mul_nonneg hη.le hu)]

theorem g_contDiffOn {η : ℝ} (hη : 0 < η) : ContDiffOn ℝ 2 (g η) (Set.Ici (0 : ℝ)) := by
  have hlin : ContDiff ℝ 2 (fun u : ℝ => η * u) := by fun_prop
  have hq : ContDiff ℝ 2 (fun u : ℝ => η * cut piece (η * u)) :=
    contDiff_const.mul (contDiff_cut_piece.comp hlin)
  apply hq.contDiffOn.congr
  intro u hu
  exact g_eq_smooth hη hu

lemma g_contDiffOn_interval {η D : ℝ} (hη : 0 < η) :
    ContDiffOn ℝ 2 (g η) (Set.Icc (0 : ℝ) D) :=
  (g_contDiffOn hη).mono (fun _ hu => hu.1)

lemma g_first_zero {η D : ℝ} (hη : 0 < η) (hD : 0 < D) :
    derivWithin (g η) (Set.Icc (0 : ℝ) D) 0 = 0 := by
  have hp1 := piece_first_zero
  rw [iteratedDeriv_piece] at hp1
  have hp : HasDerivAt piece (0 : ℝ) 0 := by
    simpa only [scaledDerivative_zero, hp1] using scaledDerivative_hasDerivAt 0 0
  have hc : HasDerivAt (cut piece) (0 : ℝ) 0 := by
    apply hp.congr_of_eventuallyEq
    filter_upwards [isOpen_Iio.mem_nhds d_pos] with u hu
    exact cut_of_le hu.le
  have hq : HasDerivAt (fun u : ℝ => η * cut piece (η * u)) (0 : ℝ) 0 := by
    have hlin : HasDerivAt (fun u : ℝ => η * u) η 0 := hasDerivAt_const_mul η
    have hc' : HasDerivAt (cut piece) (0 : ℝ) (η * 0) := by simpa using hc
    simpa using (hc'.comp 0 hlin).const_mul η
  have hw : HasDerivWithinAt (g η) (0 : ℝ) (Set.Icc (0 : ℝ) D) 0 := by
    apply hq.hasDerivWithinAt.congr
    · intro u hu
      exact g_eq_smooth hη hu.1
    · exact g_eq_smooth hη le_rfl
  exact hw.derivWithin ((uniqueDiffOn_Icc hD) 0 (by simp [hD.le]))

lemma g_eventually_zero {η u : ℝ} (hη : 0 < η) (hu : d / η < u) :
    g η =ᶠ[𝓝 u] (fun _ => 0) := by
  filter_upwards [isOpen_Ioi.mem_nhds hu] with v hv
  exact g_zero_of_gt hη hv

lemma g_derivWithin_zero {η u : ℝ} (hη : 0 < η) (S : Set ℝ) (hu : d / η < u) :
    derivWithin (g η) S u = 0 := by
  simpa only [derivWithin_fun_const, Pi.zero_apply] using
    (g_eventually_zero hη hu).derivWithin_eq_of_nhds (s := S)

lemma g_second_derivWithin_zero {η u : ℝ} (hη : 0 < η) (S : Set ℝ) (hu : d / η < u) :
    derivWithin (derivWithin (g η) S) S u = 0 := by
  have he : derivWithin (g η) S =ᶠ[𝓝 u] (fun _ => 0) := by
    filter_upwards [isOpen_Ioi.mem_nhds hu] with v hv
    exact g_derivWithin_zero hη S hv
  simpa only [derivWithin_fun_const, Pi.zero_apply] using he.derivWithin_eq_of_nhds (s := S)

/-- The published K2 smoothness and support conditions, with the same one-sided
within-derivative convention as PNT+'s Kadiri.prop_2_1. -/
structure KadiriAdmissible (D : ℝ) (f : ℝ → ℝ) : Prop where
  D_pos : 0 < D
  nonneg : ∀ u : ℝ, 0 ≤ f u
  smooth : ContDiffOn ℝ 2 f (Set.Icc (0 : ℝ) D)
  support : tsupport f ⊆ Set.Ico (0 : ℝ) D
  at_end : f D = 0
  first_zero : derivWithin f (Set.Icc (0 : ℝ) D) 0 = 0
  first_end : derivWithin f (Set.Icc (0 : ℝ) D) D = 0
  second_end : derivWithin (derivWithin f (Set.Icc (0 : ℝ) D)) (Set.Icc (0 : ℝ) D) D = 0

@[blueprint "varlamov-test-kernel-admissible"
  (title := "Varlamov, Lemma 6.1: validity of the scaled test kernel")
  (statement := /-- For every positive scale eta, $g(u)=\eta w(\eta u)$ on the
  positive half-line, extended by zero to the left, satisfies every smoothness,
  sign, support and endpoint condition of Kadiri's explicit formula, with
  $D=d/\eta+1$. -/)
  (uses := ["varlamov-kernel-c2", "varlamov-kernel-autocorrelation"])]
theorem g_admissible {η : ℝ} (hη : 0 < η) : KadiriAdmissible (d / η + 1) (g η) := by
  have hD : 0 < d / η + 1 := add_pos (div_pos d_pos hη) zero_lt_one
  have hlarge : d / η < d / η + 1 := by linarith
  refine ⟨hD, g_nonneg hη.le, g_contDiffOn_interval hη, ?_,
    g_zero_of_gt hη hlarge, g_first_zero hη hD,
    g_derivWithin_zero hη _ hlarge, g_second_derivWithin_zero hη _ hlarge⟩
  intro u hu
  have hs := g_tsupport hη hu
  exact ⟨hs.1, by linarith [hs.2]⟩

#print axioms g_admissible

end Varlamov.Kernel
