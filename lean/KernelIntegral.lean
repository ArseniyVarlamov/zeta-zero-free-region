import PrimeNumberTheoremAnd.IEANTN.Varlamov.Kernel
import Mathlib.Tactic.FunProp

namespace Varlamov.Kernel
open Real MeasureTheory

noncomputable def primitive (v x : ℝ) : ℝ :=
  (1) * x ^ 1 +
    ((-22409073 / 20000000 : ℝ) * v ^ 2) * x ^ 1 +
    ((2409073 / 20000000 : ℝ) * v ^ 4) * x ^ 1 +
    ((22409073 / 20000000 : ℝ) * v ^ 1) * x ^ 2 +
    ((-2409073 / 10000000 : ℝ) * v ^ 3) * x ^ 2 +
    ((-7469691 / 10000000 : ℝ)) * x ^ 3 +
    ((263751770906443 / 400000000000000 : ℝ) * v ^ 2) * x ^ 3 +
    ((-17995030906443 / 400000000000000 : ℝ) * v ^ 4) * x ^ 3 +
    ((-598529472719329 / 800000000000000 : ℝ) * v ^ 1) * x ^ 4 +
    ((53985092719329 / 400000000000000 : ℝ) * v ^ 3) * x ^ 4 +
    ((598529472719329 / 2000000000000000 : ℝ)) * x ^ 5 +
    ((-377895649035303 / 2000000000000000 : ℝ) * v ^ 2) * x ^ 5 +
    ((5803632719329 / 2000000000000000 : ℝ) * v ^ 4) * x ^ 5 +
    ((53985092719329 / 400000000000000 : ℝ) * v ^ 1) * x ^ 6 +
    ((-5803632719329 / 600000000000000 : ℝ) * v ^ 3) * x ^ 6 +
    ((-53985092719329 / 1400000000000000 : ℝ)) * x ^ 7 +
    ((17410898157987 / 1400000000000000 : ℝ) * v ^ 2) * x ^ 7 +
    ((-5803632719329 / 800000000000000 : ℝ) * v ^ 1) * x ^ 8 +
    ((5803632719329 / 3600000000000000 : ℝ)) * x ^ 9

lemma primitive_hasDerivAt (v x : ℝ) :
    HasDerivAt (primitive v) (q x * q (x - v)) x := by
  unfold primitive q b
  convert (((((((((((((((((((((hasDerivAt_id x).pow 1).const_mul (1)).add (((hasDerivAt_id x).pow 1).const_mul ((-22409073 / 20000000 : ℝ) * v ^ 2))).add (((hasDerivAt_id x).pow 1).const_mul ((2409073 / 20000000 : ℝ) * v ^ 4))).add (((hasDerivAt_id x).pow 2).const_mul ((22409073 / 20000000 : ℝ) * v ^ 1))).add (((hasDerivAt_id x).pow 2).const_mul ((-2409073 / 10000000 : ℝ) * v ^ 3))).add (((hasDerivAt_id x).pow 3).const_mul ((-7469691 / 10000000 : ℝ)))).add (((hasDerivAt_id x).pow 3).const_mul ((263751770906443 / 400000000000000 : ℝ) * v ^ 2))).add (((hasDerivAt_id x).pow 3).const_mul ((-17995030906443 / 400000000000000 : ℝ) * v ^ 4))).add (((hasDerivAt_id x).pow 4).const_mul ((-598529472719329 / 800000000000000 : ℝ) * v ^ 1))).add (((hasDerivAt_id x).pow 4).const_mul ((53985092719329 / 400000000000000 : ℝ) * v ^ 3))).add (((hasDerivAt_id x).pow 5).const_mul ((598529472719329 / 2000000000000000 : ℝ)))).add (((hasDerivAt_id x).pow 5).const_mul ((-377895649035303 / 2000000000000000 : ℝ) * v ^ 2))).add (((hasDerivAt_id x).pow 5).const_mul ((5803632719329 / 2000000000000000 : ℝ) * v ^ 4))).add (((hasDerivAt_id x).pow 6).const_mul ((53985092719329 / 400000000000000 : ℝ) * v ^ 1))).add (((hasDerivAt_id x).pow 6).const_mul ((-5803632719329 / 600000000000000 : ℝ) * v ^ 3))).add (((hasDerivAt_id x).pow 7).const_mul ((-53985092719329 / 1400000000000000 : ℝ)))).add (((hasDerivAt_id x).pow 7).const_mul ((17410898157987 / 1400000000000000 : ℝ) * v ^ 2))).add (((hasDerivAt_id x).pow 8).const_mul ((-5803632719329 / 800000000000000 : ℝ) * v ^ 1))).add (((hasDerivAt_id x).pow 9).const_mul ((5803632719329 / 3600000000000000 : ℝ)))) using 1 <;> (try funext y) <;> dsimp <;> ring

/-- Exact polynomial integration for all lags; the support restriction is separate. -/
lemma correlation_interval (v : ℝ) :
    (∫ x in (v - 1)..1, q x * q (x - v)) = qnorm / 10 * unit (v / 2) := by
  have hi : IntervalIntegrable (fun x => q x * q (x - v)) volume (v - 1) 1 := by
    apply Continuous.intervalIntegrable
    unfold q
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => primitive_hasDerivAt v x) hi]
  unfold primitive qnorm unit unitPoly
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_pow, Polynomial.eval_ofNat]
  ring

lemma qnorm_eq_integral : qnorm = ∫ x in (-1 : ℝ)..1, q x ^ 2 := by
  have h := correlation_interval 0
  norm_num [unit_zero] at h
  simpa [pow_two] using h.symm

noncomputable def bump (y : ℝ) : ℝ :=
  if y ∈ Set.Icc (-1 : ℝ) 1 then q y else 0

lemma bump_eq_q {y : ℝ} (hy : y ∈ Set.Icc (-1 : ℝ) 1) : bump y = q y := by
  simp [bump, hy]
lemma bump_neg_one : bump (-1) = 0 := by norm_num [bump, q]
lemma bump_one : bump 1 = 0 := by norm_num [bump, q]
lemma bump_zero_of_le_neg_one {y : ℝ} (hy : y ≤ -1) : bump y = 0 := by
  rcases eq_or_lt_of_le hy with h | h
  · simpa [h] using bump_neg_one
  · simp [bump, show ¬ y ∈ Set.Icc (-1 : ℝ) 1 from fun h' => by linarith [h'.1]]
lemma bump_zero_of_one_le {y : ℝ} (hy : 1 ≤ y) : bump y = 0 := by
  rcases eq_or_lt_of_le hy with h | h
  · simpa [← h] using bump_one
  · simp [bump, show ¬ y ∈ Set.Icc (-1 : ℝ) 1 from fun h' => by linarith [h'.2]]
lemma bump_nonneg (y : ℝ) : 0 ≤ bump y := by
  unfold bump
  split_ifs with h
  · exact q_nonneg h
  · exact le_rfl

/-- The generated polynomial is the actual autocorrelation on its support. -/
lemma correlation_full {v : ℝ} (hv : v ∈ Set.Icc (0 : ℝ) 2) :
    (∫ x : ℝ, bump x * bump (x - v)) = qnorm / 10 * unit (v / 2) := by
  have hs : Function.support (fun x => bump x * bump (x - v)) ⊆ Set.Ioc (v - 1) 1 := by
    intro x hx
    have hn : bump x * bump (x - v) ≠ 0 := hx
    constructor
    · by_contra h
      have hzero := bump_zero_of_le_neg_one (show x - v ≤ -1 by linarith)
      exact hn (by rw [hzero, mul_zero])
    · by_contra h
      have hzero := bump_zero_of_one_le (show 1 ≤ x by linarith)
      exact hn (by rw [hzero, zero_mul])
  rw [← intervalIntegral.integral_eq_integral_of_support_subset hs]
  rw [show (∫ x in (v - 1)..1, bump x * bump (x - v)) =
      (∫ x in (v - 1)..1, q x * q (x - v)) from by
    apply intervalIntegral.integral_congr
    intro x hx
    change bump x * bump (x - v) = q x * q (x - v)
    rw [Set.uIcc_of_le (show v - 1 ≤ 1 by linarith [hv.2])] at hx
    rw [bump_eq_q (show x ∈ Set.Icc (-1 : ℝ) 1 by
      constructor <;> linarith [hx.1, hx.2, hv.1]),
      bump_eq_q (show x - v ∈ Set.Icc (-1 : ℝ) 1 by
      constructor <;> linarith [hx.1, hx.2, hv.1])]]
  exact correlation_interval v

/-- On [0,d], the explicit piece agrees with the kernel in the article. -/
lemma piece_eq_autocorrelation {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) d) :
    piece u = 10 / qnorm * ∫ x : ℝ, bump x * bump (x - 2 * u / d) := by
  have hv : 2 * u / d ∈ Set.Icc (0 : ℝ) 2 := by
    constructor
    · exact div_nonneg (by linarith [hu.1]) d_pos.le
    · apply (div_le_iff₀ d_pos).mpr
      nlinarith [hu.2]
  rw [correlation_full hv]
  have hq := ne_of_gt qnorm_pos
  rw [show 2 * u / d / 2 = u / d from by ring]
  unfold piece
  field_simp [hq]

#print axioms piece_eq_autocorrelation

end Varlamov.Kernel
