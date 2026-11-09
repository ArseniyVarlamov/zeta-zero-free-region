import PrimeNumberTheoremAnd.IEANTN.Varlamov.Trigonometric
import PrimeNumberTheoremAnd.IEANTN.Varlamov.TransformBounds
import PrimeNumberTheoremAnd.IEANTN.Varlamov.KernelSupport

namespace Varlamov
open Real MeasureTheory
open scoped BigOperators

noncomputable def realW (x : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..Kernel.d, Real.exp (-x * u) * Kernel.piece u
noncomputable def smallD (μ : ℝ) : ℝ := Trigonometric.a 1 * realW (1 - μ) - realW (-μ)
noncomputable def moment (n : ℕ) : ℝ :=
  ∫ u in (0 : ℝ)..Kernel.d, u ^ n * (Trigonometric.a 1 - Real.exp u) * Kernel.piece u
noncomputable def taylorSum (μ : ℝ) : ℝ :=
  ∑ n ∈ Finset.range 9, (μ - 1) ^ n * moment n / (n.factorial : ℝ)
noncomputable def taylorUniformError : ℝ :=
  (Kernel.d / 10) ^ 9 * (10 / (Nat.factorial 9 * 9 : ℝ)) * (Trigonometric.a 1 + Real.exp Kernel.d) * 10 * Kernel.d

lemma W_real (x : ℝ) : Kernel.W (x : ℂ) = (realW x : ℂ) := by
  rw [Kernel.W, realW, ← intervalIntegral.integral_ofReal]
  apply intervalIntegral.integral_congr
  intro u _
  simp only [Complex.ofReal_mul, Complex.ofReal_exp]
  push_cast
  rfl

lemma moment_eq_article (n : ℕ) : moment n =
    ∫ u in (0 : ℝ)..Kernel.d, u ^ n * (Trigonometric.a 1 - Real.exp u) * Kernel.w u := by
  apply intervalIntegral.integral_congr
  intro u hu
  dsimp only
  rw [Set.uIcc_of_le Kernel.d_pos.le] at hu
  rw [Kernel.w_piece hu]

lemma smallD_integral (μ : ℝ) : smallD μ =
    ∫ u in (0 : ℝ)..Kernel.d,
      Real.exp ((μ - 1) * u) * (Trigonometric.a 1 - Real.exp u) * Kernel.piece u := by
  have hi (x : ℝ) : IntervalIntegrable (fun u : ℝ => Real.exp (-x * u) * Kernel.piece u)
      volume 0 Kernel.d := by
    apply Continuous.intervalIntegrable
    dsimp [Kernel.piece, Kernel.unit]
    fun_prop
  unfold smallD realW
  rw [← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_sub ((hi (1 - μ)).const_mul _) (hi (-μ))]
  apply intervalIntegral.integral_congr
  intro u _
  dsimp only
  rw [show - (1 - μ) * u = (μ - 1) * u from by ring,
    show - (-μ) * u = (μ - 1) * u + u from by ring, Real.exp_add]
  ring

lemma taylorSum_integral (μ : ℝ) : taylorSum μ =
    ∫ u in (0 : ℝ)..Kernel.d,
      (∑ n ∈ Finset.range 9, ((μ - 1) * u) ^ n / (n.factorial : ℝ)) *
        (Trigonometric.a 1 - Real.exp u) * Kernel.piece u := by
  let f : ℕ → ℝ → ℝ := fun n u =>
    (μ - 1) ^ n * (u ^ n * (Trigonometric.a 1 - Real.exp u) * Kernel.piece u) / (n.factorial : ℝ)
  have hi (n : ℕ) : IntervalIntegrable (f n) volume 0 Kernel.d := by
    apply Continuous.intervalIntegrable
    dsimp [f, Kernel.piece, Kernel.unit]
    fun_prop
  have he : taylorSum μ = ∑ n ∈ Finset.range 9, ∫ u in (0 : ℝ)..Kernel.d, f n u := by
    unfold taylorSum moment
    apply Finset.sum_congr rfl
    intro n _
    dsimp only [f]
    rw [intervalIntegral.integral_div, intervalIntegral.integral_const_mul]
  rw [he, ← intervalIntegral.integral_finsetSum (fun n _ => hi n)]
  apply intervalIntegral.integral_congr
  intro u _
  dsimp only
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n _
  dsimp [f]
  rw [mul_pow]
  ring

lemma taylor_error_numeric : taylorUniformError < 1e-12 := by
  unfold taylorUniformError
  norm_num [Trigonometric.a, Kernel.d, Nat.factorial]
  interval_decide (trust := kernel)

@[blueprint "varlamov-small-arguments"
  (title := "Varlamov, Lemma 8.2: small arguments")
  (statement := /-- If $9/10<\mu<1$, then the small-argument term is at least
  $\sum_{n=0}^8(\mu-1)^n I_n/n!-10^{-12}$, where the I_n are the actual
  moment integrals of the kernel. A slightly looser uniform Taylor bound
  than the manuscript's bound still certifies the same final error. -/)
  (uses := ["varlamov-kernel-autocorrelation", "varlamov-trigonometric-polynomial"])]
theorem small_arguments {μ : ℝ} (hμ : (9 / 10 : ℝ) < μ) (hμ1 : μ < 1) :
    taylorSum μ - 1e-12 ≤ smallD μ := by
  let D := Kernel.d
  let a := Trigonometric.a 1
  let B := (D / 10) ^ 9 * (10 / (Nat.factorial 9 * 9 : ℝ)) * (a + Real.exp D) * 10
  have hD : 0 < D := Kernel.d_pos
  have hD2 : D < 2 := by norm_num [D, Kernel.d]
  have ha : 0 < a := by norm_num [a, Trigonometric.a]
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hpoint (u : ℝ) (hu : u ∈ Set.uIoc (0 : ℝ) D) :
      |(Real.exp ((μ - 1) * u) - (∑ n ∈ Finset.range 9, ((μ - 1) * u) ^ n / (n.factorial : ℝ))) *
        (a - Real.exp u) * Kernel.piece u| ≤ B := by
    rw [Set.uIoc_of_le hD.le] at hu
    have hu0 : 0 ≤ u := hu.1.le
    have huD : u ≤ D := hu.2
    have hv : |(μ - 1) * u| ≤ D / 10 := by
      rw [abs_mul, abs_of_neg (by linarith : μ - 1 < 0), abs_of_nonneg hu0]
      nlinarith
    have hv1 : |(μ - 1) * u| ≤ 1 := by linarith
    have he := Real.exp_bound (x := (μ - 1) * u) hv1 (n := 9) (by norm_num)
    have ht : |Real.exp ((μ - 1) * u) - ∑ n ∈ Finset.range 9, ((μ - 1) * u) ^ n / (n.factorial : ℝ)| ≤
        (D / 10) ^ 9 * (10 / (Nat.factorial 9 * 9 : ℝ)) := by
      apply he.trans
      gcongr <;> norm_num
    have hw0 : 0 ≤ Kernel.piece u := by
      rw [← Kernel.w_piece ⟨hu0, huD⟩]
      exact Kernel.w_nonneg u
    have hw : |Kernel.piece u| ≤ 10 := by
      rw [abs_of_nonneg hw0, ← Kernel.w_piece ⟨hu0, huD⟩]
      exact Kernel.w_le_ten u
    have heU : |a - Real.exp u| ≤ a + Real.exp D := by
      calc
        _ ≤ |a| + |Real.exp u| := abs_sub _ _
        _ = a + Real.exp u := by rw [abs_of_pos ha, abs_of_pos (Real.exp_pos u)]
        _ ≤ _ := add_le_add le_rfl (Real.exp_le_exp.mpr huD)
    rw [abs_mul, abs_mul]
    dsimp [B]
    gcongr
  have hnorm : |smallD μ - taylorSum μ| ≤ taylorUniformError := by
    rw [smallD_integral, taylorSum_integral]
    have hi1 : IntervalIntegrable (fun u : ℝ => Real.exp ((μ - 1) * u) * (a - Real.exp u) * Kernel.piece u)
        volume 0 D := by
      apply Continuous.intervalIntegrable
      dsimp [Kernel.piece, Kernel.unit]
      fun_prop
    have hi2 : IntervalIntegrable (fun u : ℝ =>
        (∑ n ∈ Finset.range 9, ((μ - 1) * u) ^ n / (n.factorial : ℝ)) * (a - Real.exp u) * Kernel.piece u)
        volume 0 D := by
      apply Continuous.intervalIntegrable
      dsimp [Kernel.piece, Kernel.unit]
      fun_prop
    rw [← intervalIntegral.integral_sub hi1 hi2]
    have hp (u : ℝ) : Real.exp ((μ - 1) * u) * (a - Real.exp u) * Kernel.piece u -
        (∑ n ∈ Finset.range 9, ((μ - 1) * u) ^ n / (n.factorial : ℝ)) * (a - Real.exp u) * Kernel.piece u =
        (Real.exp ((μ - 1) * u) - (∑ n ∈ Finset.range 9, ((μ - 1) * u) ^ n / (n.factorial : ℝ))) *
          (a - Real.exp u) * Kernel.piece u := by ring
    rw [intervalIntegral.integral_congr (fun u _ => hp u)]
    have hn := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := D) (C := B)
      (f := fun u : ℝ => (Real.exp ((μ - 1) * u) - (∑ n ∈ Finset.range 9, ((μ - 1) * u) ^ n / (n.factorial : ℝ))) *
        (a - Real.exp u) * Kernel.piece u) (fun u hu => by
          simpa only [Real.norm_eq_abs] using hpoint u hu)
    rw [Real.norm_eq_abs] at hn
    simpa only [sub_zero, abs_of_pos hD, B, D, a, taylorUniformError, mul_assoc] using hn
  have hl := neg_abs_le (smallD μ - taylorSum μ)
  linarith [taylor_error_numeric]

#print axioms small_arguments
end Varlamov
