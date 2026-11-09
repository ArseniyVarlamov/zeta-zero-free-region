import PrimeNumberTheoremAnd.IEANTN.Varlamov.Localization
import PrimeNumberTheoremAnd.IEANTN.Varlamov.GammaSymmetry
import PrimeNumberTheoremAnd.IEANTN.Varlamov.ExplicitFormula

namespace Varlamov
open Real Complex Filter Topology
open scoped ComplexConjugate

lemma zeta_completed_order {z : ℂ} (hz : 0 < z.re) :
    meromorphicOrderAt riemannZeta z = meromorphicOrderAt completedRiemannZeta z := by
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  have hg : AnalyticAt ℂ (fun s : ℂ => (Complex.Gammaℝ s)⁻¹) z :=
    Complex.differentiable_Gammaℝ_inv.analyticAt z
  have hg0 : (Complex.Gammaℝ z)⁻¹ ≠ 0 := inv_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos hz)
  have he : riemannZeta =ᶠ[𝓝 z] (fun s : ℂ => (Complex.Gammaℝ s)⁻¹ * completedRiemannZeta s) := by
    filter_upwards [isClosed_singleton.isOpen_compl.mem_nhds hz0] with s hs
    rw [riemannZeta_def_of_ne_zero hs, div_eq_mul_inv, mul_comm]
  rw [meromorphicOrderAt_congr (he.filter_mono nhdsWithin_le_nhds)]
  exact meromorphicOrderAt_mul_of_ne_zero hg hg0

lemma zeta_order_one_sub {z : ℂ} (h0 : 0 < z.re) (h1 : z.re < 1) :
    riemannZeta.order (1 - z) = riemannZeta.order z := by
  have hφ : AnalyticAt ℂ (fun s : ℂ => 1 - s) z := by fun_prop
  have hd : deriv (fun s : ℂ => 1 - s) z = -1 := by
    simpa using ((hasDerivAt_const z (1 : ℂ)).sub (hasDerivAt_id z)).deriv
  have hcomp := meromorphicOrderAt_comp_of_deriv_ne_zero
    (f := completedRiemannZeta) hφ (by rw [hd]; norm_num)
  have he : completedRiemannZeta ∘ (fun s : ℂ => 1 - s) = completedRiemannZeta :=
    funext completedRiemannZeta_one_sub
  rw [he] at hcomp
  have h0' : 0 < (1 - z).re := by simp only [Complex.sub_re, Complex.one_re]; linarith
  unfold riemannZeta.order
  rw [zeta_completed_order h0, zeta_completed_order h0', hcomp]

/-- Adapted from the analytic-order precursor in PNT+ KadiriZeroCounting;
Mathlib's newer DifferentiableAt.conj_conj removes the custom slope proof. -/
lemma analyticAt_double_conj {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f (conj z)) :
    AnalyticAt ℂ (fun w => conj (f (conj w))) z := by
  rw [Complex.analyticAt_iff_eventually_differentiableAt] at hf ⊢
  have hc : Tendsto (conj : ℂ → ℂ) (𝓝 z) (𝓝 (conj z)) := Complex.continuous_conj.tendsto z
  filter_upwards [hc.eventually hf] with w hw
  simpa only [Function.comp_def, Complex.conj_conj] using hw.conj_conj

lemma analyticOrderAt_double_conj {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f (conj z)) :
    analyticOrderAt (fun w => conj (f (conj w))) z = analyticOrderAt f (conj z) := by
  have hcf := analyticAt_double_conj hf
  have hc : Tendsto (conj : ℂ → ℂ) (𝓝 z) (𝓝 (conj z)) := Complex.continuous_conj.tendsto z
  cases ho : analyticOrderAt f (conj z) with
  | top =>
      rw [analyticOrderAt_eq_top] at ho ⊢
      filter_upwards [hc.eventually ho] with w hw
      rw [hw, map_zero]
  | coe n =>
      rw [hf.analyticOrderAt_eq_natCast] at ho
      obtain ⟨g, hg, hg0, hfg⟩ := ho
      rw [hcf.analyticOrderAt_eq_natCast]
      refine ⟨fun w => conj (g (conj w)), analyticAt_double_conj hg, ?_, ?_⟩
      · intro h
        exact hg0 (by have := congrArg (conj : ℂ → ℂ) h; simpa using this)
      · filter_upwards [hc.eventually hfg] with w hw
        rw [hw]
        simp only [smul_eq_mul, map_mul, map_pow, map_sub, Complex.conj_conj]

lemma zeta_order_conj {z : ℂ} (hz : z ≠ 1) : riemannZeta.order (conj z) = riemannZeta.order z := by
  have hzc : conj z ≠ 1 := by intro h; apply hz; have := congrArg (conj : ℂ → ℂ) h; simpa using this
  have ha := analyticOn_riemannZeta z (by simpa using hz)
  have hac := analyticOn_riemannZeta (conj z) (by simpa using hzc)
  have he : (fun w : ℂ => conj (riemannZeta (conj w))) = riemannZeta := by
    funext w
    rw [riemannZeta_conj, Complex.conj_conj]
  have horder := analyticOrderAt_double_conj (z := conj z) (by simpa using ha)
  rw [he, Complex.conj_conj] at horder
  unfold riemannZeta.order
  rw [ha.meromorphicOrderAt_eq, hac.meromorphicOrderAt_eq, horder]

@[blueprint "varlamov-zero-reflection-order"
  (title := "Varlamov, Lemma 7.1: reflection preserves multiplicities")
  (statement := /-- Reflection $\rho\mapsto1-\bar\rho$ preserves the
  meromorphic zero order of zeta in the open critical strip. The proof
  uses Mathlib's completed functional equation and nonvanishing gamma factor. -/)
  (uses := ["varlamov-zero-localization"])]
theorem zeta_order_reflection {z : ℂ} (h0 : 0 < z.re) (h1 : z.re < 1) :
    riemannZeta.order (1 - conj z) = riemannZeta.order z := by
  rw [zeta_order_one_sub (by simpa using h0) (by simpa using h1)]
  apply zeta_order_conj
  intro h
  have hr := congrArg Complex.re h
  simp only [Complex.one_re] at hr
  linarith

abbrev NontrivialZeros := riemannZeta.zeroes_rect (Set.Ioo 0 1) Set.univ

noncomputable def reflectZero (ρ : NontrivialZeros) : NontrivialZeros :=
  ⟨1 - conj (ρ : ℂ), by
    refine ⟨?_, Set.mem_univ _, reflected_zero ρ.property.2.2 ρ.property.1.1 ρ.property.1.2⟩
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re, Set.mem_Ioo]
    constructor <;> linarith [ρ.property.1.1, ρ.property.1.2]⟩

lemma reflectZero_involutive : Function.Involutive reflectZero := by
  intro ρ
  apply Subtype.ext
  simp [reflectZero]

noncomputable def reflectZeroEquiv : NontrivialZeros ≃ NontrivialZeros :=
  { toFun := reflectZero, invFun := reflectZero,
    left_inv := reflectZero_involutive, right_inv := reflectZero_involutive }

lemma reflectZero_order (ρ : NontrivialZeros) : riemannZeta.order (reflectZero ρ) = riemannZeta.order ρ :=
  zeta_order_reflection ρ.property.1.1 ρ.property.1.2

/-- Absolute convergence after the actual finite multiplier sum. -/
theorem F_zero_sum_summable (hK2 : KadiriExplicitInput) (j : Fin 7) {h η : ℝ} {s : ℂ}
    (hh : 0 ≤ h) (hη : 0 < η) (hs : (1 / 2 : ℝ) < s.re) :
    Summable (fun ρ : NontrivialZeros => (F j h η (s - ρ)).re * (riemannZeta.order ρ : ℝ)) := by
  have hm (m : ℕ) : Summable (fun ρ : NontrivialZeros => Multiplier.coefficient j m *
      ((Kernel.W ((s + ((h * (m : ℝ) : ℝ) : ℂ) - ρ) / (η : ℂ))).re * (riemannZeta.order ρ : ℝ))) := by
    apply ((Kernel.scaled_explicit_formula hK2 hη ?_).1).mul_left
    simp only [Complex.add_re, Complex.ofReal_re]
    nlinarith [Nat.cast_nonneg (α := ℝ) m]
  apply (summable_sum (s := Finset.range (Multiplier.length j)) (fun m _ => hm m)).congr
  intro ρ
  simp only [F_re_shift_sum, Finset.sum_mul, mul_assoc]

/-- Pairing of the absolutely convergent, multiplicity-weighted zero sum.
It is valid before splitting the zero set at a height cutoff. -/
theorem zeroes_sum_pairing (hK2 : KadiriExplicitInput) (j : Fin 7) {h η : ℝ} {s : ℂ}
    (hh : 0 ≤ h) (hη : 0 < η) (hs : (1 / 2 : ℝ) < s.re) (heh : h = 2 * s.re - 1) :
    riemannZeta.zeroes_sum (Set.Ioo 0 1) Set.univ (fun ρ => (F j h η (s - ρ)).re) =
      (1 / 2) * riemannZeta.zeroes_sum (Set.Ioo 0 1) Set.univ (fun ρ => Pi j h η (s - ρ)) := by
  let f : NontrivialZeros → ℝ := fun ρ => (F j h η (s - ρ)).re * (riemannZeta.order ρ : ℝ)
  have hsum : Summable f := F_zero_sum_summable hK2 j hh hη hs
  have hmirror (ρ : NontrivialZeros) : s - (reflectZero ρ : ℂ) =
      (h : ℂ) - conj (s - (ρ : ℂ)) := by
    apply Complex.ext <;> simp [reflectZero, heh] <;> ring
  have hpair (ρ : NontrivialZeros) : Pi j h η (s - (ρ : ℂ)) * (riemannZeta.order ρ : ℝ) =
      f ρ + f (reflectZero ρ) := by
    rw [Pi, ← hmirror]
    dsimp only [f]
    rw [reflectZero_order]
    ring
  have hreindex : (∑' ρ : NontrivialZeros, f (reflectZero ρ)) = ∑' ρ : NontrivialZeros, f ρ :=
    reflectZeroEquiv.tsum_eq f
  unfold riemannZeta.zeroes_sum
  simp_rw [hpair]
  have hsref : Summable (fun ρ : NontrivialZeros => f (reflectZero ρ)) :=
    reflectZeroEquiv.summable_iff.mpr hsum
  have hadd : (∑' ρ : NontrivialZeros, (f ρ + f (reflectZero ρ))) =
      (∑' ρ : NontrivialZeros, f ρ) + (∑' ρ : NontrivialZeros, f (reflectZero ρ)) := hsum.tsum_add hsref
  rw [hadd, hreindex]
  change (∑' ρ : NontrivialZeros, f ρ) = _
  ring

theorem paired_zero_sum_summable (hK2 : KadiriExplicitInput) (j : Fin 7) {h η : ℝ} {s : ℂ}
    (hh : 0 ≤ h) (hη : 0 < η) (hs : (1 / 2 : ℝ) < s.re) (heh : h = 2 * s.re - 1) :
    Summable (fun ρ : NontrivialZeros => Pi j h η (s - ρ) * (riemannZeta.order ρ : ℝ)) := by
  let f : NontrivialZeros → ℝ := fun ρ => (F j h η (s - ρ)).re * (riemannZeta.order ρ : ℝ)
  have hf : Summable f := F_zero_sum_summable hK2 j hh hη hs
  have hfr : Summable (fun ρ : NontrivialZeros => f (reflectZero ρ)) := reflectZeroEquiv.summable_iff.mpr hf
  apply (hf.add hfr).congr
  intro ρ
  have hm : s - (reflectZero ρ : ℂ) = (h : ℂ) - conj (s - (ρ : ℂ)) := by
    apply Complex.ext <;> simp [reflectZero, heh] <;> ring
  dsimp only [f]
  rw [Pi, ← hm, reflectZero_order]
  ring

#print axioms zeta_order_reflection
#print axioms zeroes_sum_pairing
end Varlamov
