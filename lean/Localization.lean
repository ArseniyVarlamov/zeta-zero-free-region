import PrimeNumberTheoremAnd.IEANTN.Varlamov.Reduction
import PrimeNumberTheoremAnd.IEANTN.Varlamov.Bands

namespace Varlamov
open Real
open scoped ComplexConjugate

lemma reflected_zero {z : ℂ} (hz : riemannZeta z = 0)
    (h0 : 0 < z.re) (h1 : z.re < 1) : riemannZeta (1 - conj z) = 0 := by
  have hnat : ∀ n : ℕ, conj z ≠ -(n : ℂ) := by
    intro n hn
    have hre := congrArg Complex.re hn
    simp only [Complex.conj_re, Complex.neg_re, Complex.natCast_re] at hre
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hone : conj z ≠ (1 : ℂ) := by
    intro hn
    have hre := congrArg Complex.re hn
    simp only [Complex.conj_re, Complex.one_re] at hre
    linarith
  rw [riemannZeta_one_sub hnat hone, zeta_eq_zero_conj hz, mul_zero]

lemma right_half_height_gt_of_nonneg (hPT : PlattTrudgianInput) {z : ℂ}
    (hz : riemannZeta z = 0) (hhalf : 1 / 2 < z.re) (hγ : 0 ≤ z.im) : H < z.im := by
  by_contra h
  have hmem : z ∈ riemannZeta.zeroes_rect (Set.Ioo 0.5 1) (Set.Icc 0 H) :=
    ⟨⟨by linarith, zeta_re_lt_one hz⟩, ⟨hγ, le_of_not_gt h⟩, hz⟩
  exact hPT.false ⟨z, hmem⟩

lemma right_half_to_admissible (hPT : PlattTrudgianInput) {z : ℂ}
    (hz : riemannZeta z = 0) (hhalf : 1 / 2 < z.re) :
    ∃ w : ℂ, Admissible w ∧ w.re = z.re ∧ w.im = |z.im| := by
  by_cases hγ : 0 ≤ z.im
  · have hH := right_half_height_gt_of_nonneg hPT hz hhalf hγ
    refine ⟨z, ⟨hz, hhalf, ?_⟩, rfl, (abs_of_nonneg hγ).symm⟩
    have : 0 < H := by norm_num [H]
    linarith
  · have hc : riemannZeta (conj z) = 0 := zeta_eq_zero_conj hz
    have hhalf' : 1 / 2 < (conj z).re := by simpa using hhalf
    have hγ' : 0 ≤ (conj z).im := by simp only [Complex.conj_im]; linarith
    have hH := right_half_height_gt_of_nonneg hPT hc hhalf' hγ'
    refine ⟨conj z, ⟨hc, hhalf', ?_⟩, by simp, ?_⟩
    · have : 0 < H := by norm_num [H]
      linarith
    · simp [abs_of_neg (lt_of_not_ge hγ)]

lemma right_half_zero_le_sigma (hPT : PlattTrudgianInput) {A T : ℝ}
    (hA : 0 < A) (hmin : ∀ w : ℂ, Admissible w → A ≤ depth w)
    {z : ℂ} (hz : riemannZeta z = 0) (hhalf : 1 / 2 < z.re)
    (hcut : |z.im| ≤ T) : z.re ≤ 1 - A / log T := by
  obtain ⟨w, hw, hre, him⟩ := right_half_to_admissible hPT hz hhalf
  have hH := admissible_height_gt hPT hw
  have hγ1 : 1 < w.im := by norm_num [H] at hH; linarith
  have hlog : 0 < log w.im := log_pos hγ1
  have hT : w.im ≤ T := by simpa [him] using hcut
  have hlogs : log w.im ≤ log T := log_le_log (by linarith) hT
  have hd := hmin w hw
  have hd' : A / log w.im ≤ 1 - z.re := by
    apply (div_le_iff₀ hlog).mpr
    simpa [depth, hre] using hd
  have hdiv : A / log T ≤ A / log w.im :=
    div_le_div_of_nonneg_left hA.le hlog hlogs
  linarith

@[blueprint "varlamov-zero-localization"
  (title := "Varlamov, Lemma 3.3: zeros below the cutoff")
  (statement := /-- If $A$ is no larger than the depth of every admissible zero,
  and $\sigma=1-A/\log T>1/2$, every nontrivial zero of absolute ordinate at most
  $T$ lies in $1-\sigma\le\beta\le\sigma$. -/)
  (uses := ["varlamov-minimal-zero", "varlamov-band-bounds", "RH-up-to"])]
theorem zeros_below_cutoff (hPT : PlattTrudgianInput) {A T : ℝ}
    (hA : 0 < A) (hmin : ∀ w : ℂ, Admissible w → A ≤ depth w)
    (hσ : 1 / 2 < 1 - A / log T) {z : ℂ}
    (hz : riemannZeta z = 0) (h0 : 0 < z.re) (h1 : z.re < 1)
    (hcut : |z.im| ≤ T) : 1 - (1 - A / log T) ≤ z.re ∧ z.re ≤ 1 - A / log T := by
  constructor
  · by_cases hhalf : 1 / 2 ≤ z.re
    · linarith
    · have hzero := reflected_zero hz h0 h1
      have hhalf' : 1 / 2 < (1 - conj z).re := by
        simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
        linarith
      have hcut' : |(1 - conj z).im| ≤ T := by simpa using hcut
      have h := right_half_zero_le_sigma hPT hA hmin hzero hhalf' hcut'
      simp only [Complex.sub_re, Complex.one_re, Complex.conj_re] at h
      linarith
  · by_cases hhalf : z.re ≤ 1 / 2
    · linarith
    · exact right_half_zero_le_sigma hPT hA hmin hz (lt_of_not_ge hhalf) hcut

#print axioms zeros_below_cutoff

end Varlamov
