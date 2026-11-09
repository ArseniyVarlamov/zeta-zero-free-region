import PrimeNumberTheoremAnd.IEANTN.Varlamov.TransformPerturbation

namespace Varlamov
open Real
open scoped BigOperators ComplexConjugate

noncomputable def S (j : Fin 7) : ℝ := 2 * Multiplier.coeffNorm j *
  (10 + 2 * Kernel.Cminus * (etaMax j) ^ 2 / T0)

lemma F_real_perturbation (j : Fin 7) {h η v : ℝ} {z : ℂ}
    (hh : 0 ≤ h) (hη : 0 < η) (hηmax : η ≤ etaMax j)
    (hx : 0 ≤ z.re) (hv : |v| ≤ η) (hy : T0 ≤ |z.im|) :
    ‖F j h η (z + (v : ℂ)) - F j h η z‖ ≤
      Multiplier.coeffNorm j * η / z.im ^ 2 * (10 + 2 * Kernel.Cminus * (etaMax j) ^ 2 / T0) := by
  let B : ℝ := η / z.im ^ 2 * (10 + 2 * Kernel.Cminus * (etaMax j) ^ 2 / T0)
  have hW (m : ℕ) :
      ‖Kernel.W (((z + (v : ℂ)) + ((h * (m : ℝ) : ℝ) : ℂ)) / (η : ℂ)) -
        Kernel.W ((z + ((h * (m : ℝ) : ℝ) : ℂ)) / (η : ℂ))‖ ≤ B := by
    let ξ : ℂ := z + ((h * (m : ℝ) : ℝ) : ℂ)
    have hξ : 0 ≤ ξ.re := by
      simp only [ξ, Complex.add_re, Complex.ofReal_re]
      exact add_nonneg hx (mul_nonneg hh (Nat.cast_nonneg m))
    have hξim : ξ.im = z.im := by simp [ξ]
    have hk := Kernel.W_real_perturbation hη hηmax
      (show etaMax j < 1 by linarith [(etaMax_range j).2]) hξ hv (by simpa [hξim] using hy)
    have he : ((z + (v : ℂ)) + ((h * (m : ℝ) : ℝ) : ℂ)) / (η : ℂ) = (ξ + (v : ℂ)) / (η : ℂ) := by
      dsimp [ξ]
      congr 1
      ring
    rw [he]
    simpa only [B, hξim, ξ] using hk
  unfold F
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ m ∈ Finset.range (Multiplier.length j),
        ‖(Multiplier.coefficient j m : ℂ) *
          Kernel.W (((z + (v : ℂ)) + ((h * (m : ℝ) : ℝ) : ℂ)) / (η : ℂ)) -
          (Multiplier.coefficient j m : ℂ) *
          Kernel.W ((z + ((h * (m : ℝ) : ℝ) : ℂ)) / (η : ℂ))‖ := norm_sum_le _ _
    _ = ∑ m ∈ Finset.range (Multiplier.length j), |Multiplier.coefficient j m| *
        ‖Kernel.W (((z + (v : ℂ)) + ((h * (m : ℝ) : ℝ) : ℂ)) / (η : ℂ)) -
          Kernel.W ((z + ((h * (m : ℝ) : ℝ) : ℂ)) / (η : ℂ))‖ := by
      apply Finset.sum_congr rfl
      intro m _
      rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ ∑ m ∈ Finset.range (Multiplier.length j), |Multiplier.coefficient j m| * B := by
      apply Finset.sum_le_sum
      intro m _
      exact mul_le_mul_of_nonneg_left (hW m) (abs_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; unfold Multiplier.coeffNorm B; ring

@[blueprint "varlamov-off-strip"
  (title := "Varlamov, Lemma 5.3: paired transform off the strip")
  (statement := /-- For $h\in[h^-,1)$, $0<\eta\le\eta^+$,
  $-\eta\le\Re z\le h+\eta$ and $|\Im z|\ge T_0$, one has
  $\Pi(z)\ge-S\eta/(\Im z)^2$, with the constant S of the article. -/)
  (uses := ["varlamov-paired-positivity", "varlamov-transform-left-bound"])]
theorem off_strip_bound (j : Fin 7) {h η : ℝ} (hh : h ∈ Set.Ico (hMin j) 1)
    (hη : 0 < η) (hηmax : η ≤ etaMax j) {z : ℂ}
    (hx : z.re ∈ Set.Icc (-η) (h + η)) (hy : T0 ≤ |z.im|) :
    - S j * η / z.im ^ 2 ≤ Pi j h η z := by
  have hh0 : 0 < h := (hMin_pos j).trans_le hh.1
  let x : ℝ := max 0 (min h z.re)
  let v : ℝ := z.re - x
  have hx0 : 0 ≤ x := le_max_left _ _
  have hxh : x ≤ h := max_le hh0.le (min_le_left _ _)
  have hv : |v| ≤ η := by
    by_cases hz0 : z.re ≤ 0
    · have he : x = 0 := by
        simp only [x, min_eq_right (hz0.trans hh0.le), max_eq_left hz0]
      rw [show v = z.re from by dsimp [v]; rw [he]; ring]
      exact abs_le.mpr ⟨hx.1, by linarith⟩
    · by_cases hzh : z.re ≤ h
      · have he : x = z.re := by
          simp only [x, min_eq_right hzh, max_eq_right (le_of_not_ge hz0)]
        simp [v, he, hη.le]
      · have he : x = h := by
          simp only [x, min_eq_left (le_of_not_ge hzh), max_eq_right hh0.le]
        rw [show v = z.re - h from by dsimp [v]; rw [he]]
        exact abs_le.mpr ⟨by linarith, by linarith [hx.2]⟩
  let z' : ℂ := (x : ℂ) + (z.im : ℂ) * Complex.I
  let zm' : ℂ := (h : ℂ) - conj z'
  have hz' : z'.re ∈ Set.Icc (0 : ℝ) h := by simpa [z'] using And.intro hx0 hxh
  have him : z'.im = z.im := by simp [z']
  have he : z = z' + (v : ℂ) := by
    apply Complex.ext <;> simp [z', v] 
  have hmir : (h : ℂ) - conj z = zm' + (((-v : ℝ) : ℂ)) := by
    rw [he]
    dsimp [zm']
    simp
    ring
  have hxm : 0 ≤ zm'.re := by
    simp only [zm', Complex.sub_re, Complex.ofReal_re, Complex.conj_re]
    linarith [hz'.2]
  have himm : zm'.im = z.im := by simp [zm', him]
  have h1 := F_real_perturbation j hh0.le hη hηmax hz'.1 hv (by simpa [him] using hy)
  rw [← he, him] at h1
  have h2 := F_real_perturbation j hh0.le hη hηmax hxm
    (show |-v| ≤ η by simpa using hv) (by simpa [himm] using hy)
  rw [← hmir, himm] at h2
  let B : ℝ := Multiplier.coeffNorm j * η / z.im ^ 2 * (10 + 2 * Kernel.Cminus * (etaMax j) ^ 2 / T0)
  change ‖F j h η z - F j h η z'‖ ≤ B at h1
  change ‖F j h η ((h : ℂ) - conj z) - F j h η zm'‖ ≤ B at h2
  have hr1 := Complex.abs_re_le_norm (F j h η z - F j h η z')
  have hr2 := Complex.abs_re_le_norm (F j h η ((h : ℂ) - conj z) - F j h η zm')
  have hn1 := neg_abs_le (F j h η z - F j h η z').re
  have hn2 := neg_abs_le (F j h η ((h : ℂ) - conj z) - F j h η zm').re
  simp only [Complex.sub_re] at hr1 hr2 hn1 hn2
  have hp := paired_positivity j hh hη hηmax hz'
  change 0 ≤ (F j h η z').re + (F j h η zm').re at hp
  have hlow : -2 * B ≤ Pi j h η z := by
    unfold Pi
    linarith
  calc
    - S j * η / z.im ^ 2 = -2 * B := by unfold S B; ring
    _ ≤ Pi j h η z := hlow

#print axioms off_strip_bound

end Varlamov
