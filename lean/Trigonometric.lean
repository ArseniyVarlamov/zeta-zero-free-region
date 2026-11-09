import PrimeNumberTheoremAnd.IEANTN.Varlamov.Definitions
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Tactic.FinCases

/-! # The degree-12 nonnegative trigonometric polynomial (C3)

The generated square factorization is proved by exact polynomial arithmetic.
The generator is not part of the trusted proof.
-/

namespace Varlamov.Trigonometric
open Real Polynomial
open scoped BigOperators
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

noncomputable def c (k : ℕ) : ℝ :=
  match k with
  | 0 => 3107391881
  | 1 => -5311531843
  | 2 => -1551584903
  | 3 => 17515944216
  | 4 => 5809729718
  | 5 => -38311065182
  | 6 => -14579538641
  | 7 => 172588837119
  | 8 => 453058678886
  | 9 => 619311376818
  | 10 => 537000910627
  | 11 => 291152319789
  | 12 => 78762658700
  | _ => 0

noncomputable def norm : ℝ := 1000000000000529836702335

noncomputable def a (k : ℕ) : ℝ :=
  match k with
  | 0 => 1
  | 1 => (579010044340076601089576 / 333333333333509945567445)
  | 2 => (372472425610793918366698 / 333333333333509945567445)
  | 3 => (495623914497151388166062 / 1000000000000529836702335)
  | 4 => (120554824393494214603934 / 1000000000000529836702335)
  | 5 => (1000228859347402 / 1000000000000529836702335)
  | 6 => (199996493868992 / 200000000000105967340467)
  | 7 => (3499376197933710183214 / 333333333333509945567445)
  | 8 => (126334835847158052526 / 22222222222233996371163)
  | 9 => (199941953501132 / 200000000000105967340467)
  | 10 => (199956116908864 / 200000000000105967340467)
  | 11 => (972747969844526498018 / 1000000000000529836702335)
  | 12 => (97898578468141605880 / 200000000000105967340467)
  | _ => 0

noncomputable def realFactor (y : ℝ) : ℝ :=
  (19868672102) +
    (913590323449) * y ^ 1 +
    (6369243677510) * y ^ 2 +
    (237405094588) * y ^ 3 +
    (-75404046628528) * y ^ 4 +
    (-111100069994912) * y ^ 5 +
    (202706084090112) * y ^ 6 +
    (474207265054272) * y ^ 7 +
    (-84962157770752) * y ^ 8 +
    (-661341220060416) * y ^ 9 +
    (-208973308811776) * y ^ 10 +
    (298139975463936) * y ^ 11 +
    (161305925017600) * y ^ 12

noncomputable def imagFactor (y : ℝ) : ℝ :=
  (94431678669) +
    (686568450258) * y ^ 1 +
    (-2631387235476) * y ^ 2 +
    (-27108883879184) * y ^ 3 +
    (-28830652657952) * y ^ 4 +
    (132268115968320) * y ^ 5 +
    (255339145823040) * y ^ 6 +
    (-128959090295040) * y ^ 7 +
    (-512271232328448) * y ^ 8 +
    (-128320346302976) * y ^ 9 +
    (298139975463936) * y ^ 10 +
    (161305925017600) * y ^ 11

lemma T2_eval (y : ℝ) : (Polynomial.Chebyshev.T ℝ 2).eval y = (-1) +
    (2) * y ^ 2 := by
  have h := congrArg (Polynomial.eval y) (Polynomial.Chebyshev.T_add_two ℝ (0 : ℤ))
  norm_num [Polynomial.Chebyshev.T_zero, Polynomial.Chebyshev.T_one, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X] at h
  linear_combination h

lemma T3_eval (y : ℝ) : (Polynomial.Chebyshev.T ℝ 3).eval y = (-3) * y ^ 1 +
    (4) * y ^ 3 := by
  have h := congrArg (Polynomial.eval y) (Polynomial.Chebyshev.T_add_two ℝ (1 : ℤ))
  norm_num [Polynomial.Chebyshev.T_zero, Polynomial.Chebyshev.T_one, T2_eval, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X] at h
  linear_combination h

lemma T4_eval (y : ℝ) : (Polynomial.Chebyshev.T ℝ 4).eval y = (1) +
    (-8) * y ^ 2 +
    (8) * y ^ 4 := by
  have h := congrArg (Polynomial.eval y) (Polynomial.Chebyshev.T_add_two ℝ (2 : ℤ))
  norm_num [Polynomial.Chebyshev.T_zero, Polynomial.Chebyshev.T_one, T2_eval, T3_eval, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X] at h
  linear_combination h

lemma T5_eval (y : ℝ) : (Polynomial.Chebyshev.T ℝ 5).eval y = (5) * y ^ 1 +
    (-20) * y ^ 3 +
    (16) * y ^ 5 := by
  have h := congrArg (Polynomial.eval y) (Polynomial.Chebyshev.T_add_two ℝ (3 : ℤ))
  norm_num [Polynomial.Chebyshev.T_zero, Polynomial.Chebyshev.T_one, T2_eval, T3_eval, T4_eval, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X] at h
  linear_combination h

lemma T6_eval (y : ℝ) : (Polynomial.Chebyshev.T ℝ 6).eval y = (-1) +
    (18) * y ^ 2 +
    (-48) * y ^ 4 +
    (32) * y ^ 6 := by
  have h := congrArg (Polynomial.eval y) (Polynomial.Chebyshev.T_add_two ℝ (4 : ℤ))
  norm_num [Polynomial.Chebyshev.T_zero, Polynomial.Chebyshev.T_one, T2_eval, T3_eval, T4_eval, T5_eval, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X] at h
  linear_combination h

lemma T7_eval (y : ℝ) : (Polynomial.Chebyshev.T ℝ 7).eval y = (-7) * y ^ 1 +
    (56) * y ^ 3 +
    (-112) * y ^ 5 +
    (64) * y ^ 7 := by
  have h := congrArg (Polynomial.eval y) (Polynomial.Chebyshev.T_add_two ℝ (5 : ℤ))
  norm_num [Polynomial.Chebyshev.T_zero, Polynomial.Chebyshev.T_one, T2_eval, T3_eval, T4_eval, T5_eval, T6_eval, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X] at h
  linear_combination h

lemma T8_eval (y : ℝ) : (Polynomial.Chebyshev.T ℝ 8).eval y = (1) +
    (-32) * y ^ 2 +
    (160) * y ^ 4 +
    (-256) * y ^ 6 +
    (128) * y ^ 8 := by
  have h := congrArg (Polynomial.eval y) (Polynomial.Chebyshev.T_add_two ℝ (6 : ℤ))
  norm_num [Polynomial.Chebyshev.T_zero, Polynomial.Chebyshev.T_one, T2_eval, T3_eval, T4_eval, T5_eval, T6_eval, T7_eval, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X] at h
  linear_combination h

lemma T9_eval (y : ℝ) : (Polynomial.Chebyshev.T ℝ 9).eval y = (9) * y ^ 1 +
    (-120) * y ^ 3 +
    (432) * y ^ 5 +
    (-576) * y ^ 7 +
    (256) * y ^ 9 := by
  have h := congrArg (Polynomial.eval y) (Polynomial.Chebyshev.T_add_two ℝ (7 : ℤ))
  norm_num [Polynomial.Chebyshev.T_zero, Polynomial.Chebyshev.T_one, T2_eval, T3_eval, T4_eval, T5_eval, T6_eval, T7_eval, T8_eval, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X] at h
  linear_combination h

lemma T10_eval (y : ℝ) : (Polynomial.Chebyshev.T ℝ 10).eval y = (-1) +
    (50) * y ^ 2 +
    (-400) * y ^ 4 +
    (1120) * y ^ 6 +
    (-1280) * y ^ 8 +
    (512) * y ^ 10 := by
  have h := congrArg (Polynomial.eval y) (Polynomial.Chebyshev.T_add_two ℝ (8 : ℤ))
  norm_num [Polynomial.Chebyshev.T_zero, Polynomial.Chebyshev.T_one, T2_eval, T3_eval, T4_eval, T5_eval, T6_eval, T7_eval, T8_eval, T9_eval, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X] at h
  linear_combination h

lemma T11_eval (y : ℝ) : (Polynomial.Chebyshev.T ℝ 11).eval y = (-11) * y ^ 1 +
    (220) * y ^ 3 +
    (-1232) * y ^ 5 +
    (2816) * y ^ 7 +
    (-2816) * y ^ 9 +
    (1024) * y ^ 11 := by
  have h := congrArg (Polynomial.eval y) (Polynomial.Chebyshev.T_add_two ℝ (9 : ℤ))
  norm_num [Polynomial.Chebyshev.T_zero, Polynomial.Chebyshev.T_one, T2_eval, T3_eval, T4_eval, T5_eval, T6_eval, T7_eval, T8_eval, T9_eval, T10_eval, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X] at h
  linear_combination h

lemma T12_eval (y : ℝ) : (Polynomial.Chebyshev.T ℝ 12).eval y = (1) +
    (-72) * y ^ 2 +
    (840) * y ^ 4 +
    (-3584) * y ^ 6 +
    (6912) * y ^ 8 +
    (-6144) * y ^ 10 +
    (2048) * y ^ 12 := by
  have h := congrArg (Polynomial.eval y) (Polynomial.Chebyshev.T_add_two ℝ (10 : ℤ))
  norm_num [Polynomial.Chebyshev.T_zero, Polynomial.Chebyshev.T_one, T2_eval, T3_eval, T4_eval, T5_eval, T6_eval, T7_eval, T8_eval, T9_eval, T10_eval, T11_eval, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X] at h
  linear_combination h

noncomputable def P (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range 13, a k * cos ((k : ℝ) * x)

lemma norm_pos : 0 < norm := by norm_num [norm]
lemma norm_eq : norm = ∑ k ∈ Finset.range 13, (c k) ^ 2 := by
  norm_num [norm, c, Finset.sum_range_succ]
lemma a_zero : a 0 = 1 := by norm_num [a]
lemma a_nonneg (k : Fin 13) : 0 ≤ a k := by fin_cases k <;> norm_num [a]
lemma a_autocorrelation (k : Fin 12) :
    a (k.val + 1) = 2 * (∑ l ∈ Finset.range (12 - k.val), c l * c (l + k.val + 1)) / norm := by
  fin_cases k <;> norm_num [a, c, norm, Finset.sum_range_succ]

lemma a_one : a 1 = 579010044340076601089576 / 333333333333509945567445 := by
  norm_num [a]
lemma a_plus : (∑ k ∈ Finset.range 12, a (k + 1)) =
    697654317962413463864378 / 200000000000105967340467 := by
  norm_num [a, Finset.sum_range_succ]

lemma algebraic_factorization (y : ℝ) :
    norm * (∑ k ∈ Finset.range 13,
      a k * (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval y) =
        (realFactor y) ^ 2 + (1 - y ^ 2) * (imagFactor y) ^ 2 := by
  norm_num [norm, a, realFactor, imagFactor, Finset.sum_range_succ,
    T2_eval, T3_eval, T4_eval, T5_eval, T6_eval, T7_eval, T8_eval, T9_eval, T10_eval, T11_eval, T12_eval, Polynomial.Chebyshev.T_zero, Polynomial.Chebyshev.T_one, Polynomial.eval_add, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C]
  ring

lemma square_decomposition (x : ℝ) :
    norm * P x = (realFactor (cos x)) ^ 2 + (sin x * imagFactor (cos x)) ^ 2 := by
  have h := algebraic_factorization (cos x)
  simp only [Polynomial.Chebyshev.T_real_cos, Int.cast_natCast] at h
  have hs : (sin x) ^ 2 = 1 - (cos x) ^ 2 := by nlinarith [sin_sq_add_cos_sq x]
  simpa only [P, mul_pow, hs] using h

@[blueprint "varlamov-trigonometric-polynomial"
  (title := "Varlamov, degree-12 nonnegative trigonometric polynomial")
  (statement := /-- The exact coefficients from the article have $a_0=1$,
  $a_k\ge0$, and $P(x)=\sum_{k=0}^{12}a_k\cos(kx)\ge0$ for every real x. -/)]
theorem P_nonneg (x : ℝ) : 0 ≤ P x := by
  have h : 0 ≤ norm * P x := by rw [square_decomposition]; positivity
  exact (mul_nonneg_iff_of_pos_left norm_pos).mp h

#print axioms P_nonneg

end Varlamov.Trigonometric
