import PrimeNumberTheoremAnd.IEANTN.Varlamov.Definitions
import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Gamma.DigammaSeries
import Mathlib.NumberTheory.Harmonic.Bounds

/-! # Digamma series tails and growth in the whole right half-plane

The existing PNT+ series theorem is reused. Its growth theorem controls fixed
vertical strips; here the splitting index depends on the full norm of z,
which gives the uniform half-plane estimate needed in Lemma 6.2.
-/

namespace Varlamov
open Real Filter Topology
open scoped BigOperators

noncomputable def digammaSummand (z : ℂ) (n : ℕ) : ℂ :=
  ((n : ℂ) + 1)⁻¹ - (z + n)⁻¹

lemma digamma_hasSum {a : ℝ} (ha : 0 < a) {z : ℂ} (hz : a ≤ z.re) :
    HasSum (digammaSummand z) (Complex.digamma z + Real.eulerMascheroniConstant) := by
  have hre : 0 < z.re := ha.trans_le hz
  have hp : ∀ n : ℕ, z ≠ -(n : ℂ) := by
    intro n h
    rw [h] at hre
    simp only [Complex.neg_re, Complex.natCast_re] at hre
    linarith [(show (0 : ℝ) ≤ n from Nat.cast_nonneg n)]
  have h := Complex.hasSum_digamma hp
  convert h using 1
  funext n
  simp only [digammaSummand, one_div]
  congr 1
  congr 1
  ring

lemma digamma_norm_summable {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    {z : ℂ} (hz : a ≤ z.re) : Summable (fun n : ℕ => ‖digammaSummand z n‖) := by
  have hm : Summable (fun n : ℕ => (‖z‖ + 1) / (a * ((n : ℝ) + 1) ^ 2)) := by
    refine (Complex.summable_one_div_natCast_add_one_sq.mul_left ((‖z‖ + 1) / a)).congr fun n => ?_
    rw [mul_one_div, div_div]
  exact Summable.of_nonneg_of_le (fun n => norm_nonneg _)
    (fun n => Complex.norm_inv_add_one_sub_inv_le ha ha1 hz (le_refl ‖z‖) n) hm

lemma digamma_tail_norm {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    {z : ℂ} (hz : a ≤ z.re) {N : ℕ} (hN : 1 ≤ N) :
    ‖∑' i : ℕ, digammaSummand z (i + N)‖ ≤ (‖z‖ + 1) / (a * (N : ℝ)) := by
  have hn := (summable_nat_add_iff N).mpr (digamma_norm_summable ha ha1 hz)
  have hm : Summable (fun i : ℕ => (‖z‖ + 1) / (a * ((((i + N : ℕ) : ℝ)) + 1) ^ 2)) := by
    have hbase : Summable (fun n : ℕ => (‖z‖ + 1) / (a * ((n : ℝ) + 1) ^ 2)) := by
      refine (Complex.summable_one_div_natCast_add_one_sq.mul_left ((‖z‖ + 1) / a)).congr fun n => ?_
      rw [mul_one_div, div_div]
    exact (summable_nat_add_iff N).mpr hbase
  calc
    _ ≤ ∑' i : ℕ, ‖digammaSummand z (i + N)‖ := norm_tsum_le_tsum_norm hn
    _ ≤ ∑' i : ℕ, (‖z‖ + 1) / (a * ((((i + N : ℕ) : ℝ)) + 1) ^ 2) :=
      hn.tsum_le_tsum (fun i => Complex.norm_inv_add_one_sub_inv_le ha ha1 hz (le_refl ‖z‖) (i + N)) hm
    _ = (‖z‖ + 1) / a * ∑' i : ℕ, 1 / ((((i + N : ℕ) : ℝ)) + 1) ^ 2 := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro i
      rw [mul_one_div, div_div]
    _ ≤ (‖z‖ + 1) / a * (N : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_left (Complex.tsum_one_div_natCast_add_add_one_sq_le hN) (by positivity)
    _ = _ := by ring

/-- Uniform finite-series error, suitable for an integral limit argument. -/
theorem digamma_partial_error {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    {z : ℂ} (hz : a ≤ z.re) {N : ℕ} (hN : 1 ≤ N) :
    ‖Complex.digamma z + Real.eulerMascheroniConstant -
      ∑ n ∈ Finset.range N, digammaSummand z n‖ ≤ (‖z‖ + 1) / (a * (N : ℝ)) := by
  have hs := digamma_hasSum ha hz
  have he := hs.summable.sum_add_tsum_nat_add N
  rw [hs.tsum_eq] at he
  have hid : Complex.digamma z + Real.eulerMascheroniConstant -
      (∑ n ∈ Finset.range N, digammaSummand z n) = ∑' i : ℕ, digammaSummand z (i + N) := by
    linear_combination - he
  rw [hid]
  exact digamma_tail_norm ha ha1 hz hN

@[blueprint "varlamov-digamma-growth"
  (title := "Varlamov, Lemma 6.2: uniform digamma growth")
  (statement := /-- For every $\alpha>0$, the bound
  $|\psi(z)|=O_\alpha(\log(2+|z|))$ holds uniformly for $\Re z\ge\alpha$. -/)]
theorem digamma_halfplane_growth {α : ℝ} (hα : 0 < α) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, α ≤ z.re →
      ‖Complex.digamma z‖ ≤ C * log (2 + ‖z‖) := by
  let a : ℝ := min α 1
  have ha : 0 < a := lt_min hα zero_lt_one
  have ha1 : a ≤ 1 := min_le_right _ _
  let B : ℝ := |Real.eulerMascheroniConstant| + 3 / a
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hlog2 : 0 < log 2 := log_pos (by norm_num)
  refine ⟨B / log 2 + 2 / a, by positivity, ?_⟩
  intro z hz
  have hza : a ≤ z.re := (min_le_left α 1).trans hz
  let N : ℕ := ⌈‖z‖⌉₊ + 1
  have hN1 : 1 ≤ N := Nat.le_add_left 1 _
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hNlower : ‖z‖ + 1 ≤ (N : ℝ) := by
    dsimp [N]
    push_cast
    linarith [Nat.le_ceil ‖z‖]
  have hNupper : (N : ℝ) ≤ ‖z‖ + 2 := by
    dsimp [N]
    push_cast
    linarith [Nat.ceil_lt_add_one (norm_nonneg z)]
  let L : ℝ := log (2 + ‖z‖)
  have hlog : log 2 ≤ L := log_le_log (by norm_num) (by linarith [norm_nonneg z])
  have hhead : (∑ n ∈ Finset.range N, ‖digammaSummand z n‖) ≤ 2 / a + 2 / a * L := by
    calc
      _ ≤ ∑ n ∈ Finset.range N, 2 / (a * ((n : ℝ) + 1)) :=
        Finset.sum_le_sum (fun n _ => Complex.norm_inv_add_one_sub_inv_le' ha ha1 hza n)
      _ = 2 / a * ∑ n ∈ Finset.range N, ((n : ℝ) + 1)⁻¹ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n _
        rw [← div_div, div_eq_mul_inv]
      _ = 2 / a * ((harmonic N : ℚ) : ℝ) := by rw [Complex.sum_inv_natCast_add_one_real]
      _ ≤ 2 / a * (1 + log N) := mul_le_mul_of_nonneg_left (harmonic_le_one_add_log N) (by positivity)
      _ ≤ 2 / a * (1 + L) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have hL : log (N : ℝ) ≤ L := log_le_log hNpos (by linarith)
        linarith
      _ = _ := by ring
  have htail : ‖∑' i : ℕ, digammaSummand z (i + N)‖ ≤ 1 / a := by
    apply (digamma_tail_norm ha ha1 hza hN1).trans
    rw [div_le_div_iff₀ (mul_pos ha hNpos) ha]
    nlinarith
  have hs := digamma_hasSum ha hza
  have hsplit := hs.summable.sum_add_tsum_nat_add N
  have hsum : ‖∑' n : ℕ, digammaSummand z n‖ ≤ (2 / a + 2 / a * L) + 1 / a := by
    rw [← hsplit]
    exact (norm_add_le _ _).trans (add_le_add ((norm_sum_le _ _).trans hhead) htail)
  have hEq : Complex.digamma z = (∑' n : ℕ, digammaSummand z n) -
      (Real.eulerMascheroniConstant : ℂ) := by rw [hs.tsum_eq]; ring
  have hpsi : ‖Complex.digamma z‖ ≤ (2 / a) * L + B := by
    rw [hEq]
    have h := norm_sub_le (∑' n : ℕ, digammaSummand z n) (Real.eulerMascheroniConstant : ℂ)
    simp only [Complex.norm_real, Real.norm_eq_abs] at h
    calc
      _ ≤ ‖∑' n : ℕ, digammaSummand z n‖ + |Real.eulerMascheroniConstant| := h
      _ ≤ (2 / a + 2 / a * L + 1 / a) + |Real.eulerMascheroniConstant| := add_le_add hsum le_rfl
      _ = _ := by dsimp [B]; ring
  have hBabs : B ≤ B / log 2 * L := by
    calc
      B = B / log 2 * log 2 := by field_simp
      _ ≤ B / log 2 * L := mul_le_mul_of_nonneg_left hlog (div_nonneg hB hlog2.le)
  exact hpsi.trans (by nlinarith)

#print axioms digamma_partial_error
#print axioms digamma_halfplane_growth

end Varlamov
