import PrimeNumberTheoremAnd.IEANTN.Varlamov.DigammaBounds

namespace Varlamov
open Real Filter Topology
open scoped BigOperators

noncomputable def realDigamma (x : ℝ) : ℝ := (Complex.digamma (x : ℂ)).re

lemma digammaSummand_real (x : ℝ) (n : ℕ) :
    (digammaSummand (x : ℂ) n).re = ((n : ℝ) + 1)⁻¹ - (x + n)⁻¹ := by
  have he : digammaSummand (x : ℂ) n =
      ((((n : ℝ) + 1)⁻¹ - (x + n)⁻¹ : ℝ) : ℂ) := by
    unfold digammaSummand
    push_cast
    rfl
  rw [he, Complex.ofReal_re]

/-- Monotonicity used for the real gamma terms in Lemma 7.2, proved from the
already formalized digamma series, rather than assumed as an extra input. -/
theorem realDigamma_monotoneOn : MonotoneOn realDigamma (Set.Ioi 0) := by
  intro x hx y hy hxy
  change 0 < x at hx
  change 0 < y at hy
  have hxS := digamma_hasSum hx (show x ≤ (x : ℂ).re from le_rfl)
  have hyS := digamma_hasSum hy (show y ≤ (y : ℂ).re from le_rfl)
  have htx := Complex.continuous_re.tendsto _ |>.comp hxS.tendsto_sum_nat
  have hty := Complex.continuous_re.tendsto _ |>.comp hyS.tendsto_sum_nat
  have hb (N : ℕ) : (∑ n ∈ Finset.range N, digammaSummand (x : ℂ) n).re ≤
      (∑ n ∈ Finset.range N, digammaSummand (y : ℂ) n).re := by
    simp only [Complex.re_sum, digammaSummand_real]
    apply Finset.sum_le_sum
    intro n _
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hi : (y + (n : ℝ))⁻¹ ≤ (x + n)⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le (by positivity : 0 < x + (n : ℝ)) (by linarith : x + (n : ℝ) ≤ y + n)
    linarith
  have hle := le_of_tendsto_of_tendsto htx hty (Filter.Eventually.of_forall hb)
  simpa only [Complex.add_re, Complex.ofReal_re, realDigamma, add_le_add_iff_right] using hle

/-- Published Kadiri (2005), equation (28), p.323.
https://doi.org/10.4064/aa117-4-1 . This is a theorem parameter. -/
def KadiriDigammaInput : Prop :=
  ∀ x y : ℝ, 0 < x → x ^ 2 < y ^ 2 → ∃ r : ℝ,
    (Complex.digamma ((x : ℂ) + (y : ℂ) * Complex.I)).re =
      Real.log |y|-x / (2 * (x ^ 2 + y ^ 2)) + r ∧
    |r| ≤ 1 / (12 * x * |y|) + x ^ 2 / (2 * y ^ 2)

/-- The uniform high-line digamma error used in C8. The numerical bound is
proved by rational inequalities with H=3*10^12. -/
theorem digamma_high_error (hK3 : KadiriDigammaInput) {x y : ℝ}
    (hx : 1 ≤ x) (hx9 : x ≤ 9) (hy : H / 2 ≤ |y|) :
    |(Complex.digamma ((x : ℂ) + (y : ℂ) * Complex.I)).re - Real.log (|y|)| < 1e-10 := by
  have hH : (0 : ℝ) < H / 2 := by norm_num [H]
  have hY : 0 < |y| := hH.trans_le hy
  have hsq : (H / 2) ^ 2 ≤ y ^ 2 := by nlinarith [sq_abs y]
  have hx0 : 0 < x := by linarith
  have hxy : x ^ 2 < y ^ 2 := by norm_num [H] at hsq; nlinarith [sq_nonneg x]
  obtain ⟨r, heq, hr⟩ := hK3 x y hx0 hxy
  have hterm : |x / (2 * (x ^ 2 + y ^ 2))| ≤ 9 / (2 * (H / 2) ^ 2) := by
    rw [abs_of_pos (by positivity : 0 < x / (2 * (x ^ 2 + y ^ 2)))]
    gcongr
    nlinarith [sq_nonneg x]
  have hrbound : |r| ≤ 1 / (12 * (H / 2)) + 9 ^ 2 / (2 * (H / 2) ^ 2) := by
    apply hr.trans
    apply add_le_add
    · apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      nlinarith
    · gcongr
  calc
    _ = |-(x / (2 * (x ^ 2 + y ^ 2))) + r| := by rw [heq]; congr 1; ring
    _ ≤ |x / (2 * (x ^ 2 + y ^ 2))| + |r| := by simpa only [abs_neg] using abs_add_le (-(x / (2 * (x ^ 2 + y ^ 2)))) r
    _ ≤ 9 / (2 * (H / 2) ^ 2) + (1 / (12 * (H / 2)) + 9 ^ 2 / (2 * (H / 2) ^ 2)) := add_le_add hterm hrbound
    _ < _ := by norm_num [H]

#print axioms realDigamma_monotoneOn
#print axioms digamma_high_error
end Varlamov
