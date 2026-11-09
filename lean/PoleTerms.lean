import PrimeNumberTheoremAnd.IEANTN.Varlamov.OffStrip
import PrimeNumberTheoremAnd.IEANTN.Varlamov.Trigonometric

namespace Varlamov
open Real
open scoped BigOperators

/-- A deliberately coarse kernel-certified enclosure suffices for C9. -/
lemma Cminus_upper : Kernel.Cminus < (1000000 : ℝ) := by
  have he : exp Kernel.d < 4 := by
    unfold Kernel.d
    interval_decide (trust := kernel)
  unfold Kernel.Cminus
  rw [pair_second_value, pair_third_value]
  norm_num [Kernel.M4star, Kernel.unitM4, Kernel.d] at he ⊢
  nlinarith

lemma coeffNorm_upper (j : Fin 7) : Multiplier.coeffNorm j < 10 := by
  fin_cases j <;> norm_num [Multiplier.coeffNorm, Multiplier.length,
    Multiplier.coefficient, Multiplier.coefficient1, Multiplier.coefficient2,
    Multiplier.coefficient3, Multiplier.coefficient4, Multiplier.coefficient5,
    Multiplier.coefficient6, Multiplier.coefficient7, Finset.sum_range_succ]

lemma degree_upper (j : Fin 7) : Multiplier.length j ≤ 15 := by
  unfold Multiplier.length
  split_ifs <;> norm_num

/-- A single scaled pole term, before the finite multiplier sums. -/
lemma W_pole_re_bound {η : ℝ} {z : ℂ} (hη : 0 < η)
    (hx : -η ≤ z.re) (hxabs : |z.re| ≤ 14) (hy : H ≤ |z.im|) :
    |(Kernel.W (z / (η : ℂ))).re| ≤ 140 * η / H ^ 2 + Kernel.Cminus * η ^ 3 / H ^ 3 := by
  have hH : (0 : ℝ) < H := by norm_num [H]
  have hy0 : 0 < |z.im| := hH.trans_le hy
  have hz0 : z ≠ 0 := by intro h; simp [h] at hy0
  have hηC : (η : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hη)
  have hξ0 : z / (η : ℂ) ≠ 0 := div_ne_zero hz0 hηC
  have hξre : -1 ≤ (z / (η : ℂ)).re := by
    rw [Complex.div_ofReal_re]
    exact (le_div_iff₀ hη).mpr (by linarith)
  have hrem := Kernel.W_left_bound hξ0 hξre
  have hremScaled : ‖Kernel.W (z / (η : ℂ)) - 10 / (z / (η : ℂ))‖ ≤
      Kernel.Cminus * η ^ 3 / ‖z‖ ^ 3 := by
    convert hrem using 1
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hη, div_pow,
      div_div_eq_mul_div]
  have himnorm : H ≤ ‖z‖ := hy.trans (Complex.abs_im_le_norm z)
  have hrem' : ‖Kernel.W (z / (η : ℂ)) - 10 / (z / (η : ℂ))‖ ≤ Kernel.Cminus * η ^ 3 / H ^ 3 :=
    hremScaled.trans (by gcongr; exact mul_nonneg Kernel.Cminus_pos.le (pow_nonneg hη.le 3))
  have hmain : |((10 : ℂ) / (z / (η : ℂ))).re| ≤ 140 * η / H ^ 2 := by
    rw [show (10 : ℂ) / (z / (η : ℂ)) = ((10 * η : ℝ) : ℂ) / z from by push_cast; field_simp]
    simp only [Complex.div_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, zero_div, add_zero,
      Complex.normSq_apply]
    rw [← pow_two, ← pow_two]
    have hdenpos : 0 < z.re ^ 2 + z.im ^ 2 := by nlinarith [sq_abs z.im]
    rw [abs_div, abs_mul, abs_of_pos (by positivity : 0 < 10 * η), abs_of_pos hdenpos]
    have hden : H ^ 2 ≤ z.re ^ 2 + z.im ^ 2 := by nlinarith [sq_abs z.im, sq_nonneg z.re]
    calc
      _ ≤ (10 * η) * 14 / H ^ 2 := by gcongr
      _ = _ := by ring
  have hre := (Complex.abs_re_le_norm (Kernel.W (z / (η : ℂ)) - 10 / (z / (η : ℂ)))).trans hrem'
  rw [Complex.sub_re] at hre
  calc
    _ = |(Kernel.W (z / (η : ℂ)) - 10 / (z / (η : ℂ))).re + ((10 : ℂ) / (z / (η : ℂ))).re| := by
      rw [Complex.sub_re, sub_add_cancel]
    _ ≤ |(Kernel.W (z / (η : ℂ)) - 10 / (z / (η : ℂ))).re| + |((10 : ℂ) / (z / (η : ℂ))).re| := abs_add_le _ _
    _ ≤ _ := by simpa only [add_comm] using add_le_add ((Complex.abs_re_le_norm _).trans hrem') hmain

lemma F_pole_re_bound (j : Fin 7) {σ h η t : ℝ}
    (hη : 0 < η) (hσ : 1 - η ≤ σ) (hσ1 : σ ≤ 1) (hη1 : η ≤ 1)
    (hh : 0 ≤ h) (hh1 : h ≤ 1) (ht : H ≤ |t|) :
    |(F j h η (((σ - 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re| ≤
      Multiplier.coeffNorm j * (140 * η / H ^ 2 + Kernel.Cminus * η ^ 3 / H ^ 3) := by
  let B := 140 * η / H ^ 2 + Kernel.Cminus * η ^ 3 / H ^ 3
  have hb (m : ℕ) (hm : m ∈ Finset.range (Multiplier.length j)) :
      |(Kernel.W (((((σ - 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I) +
        ((h * (m : ℝ) : ℝ) : ℂ)) / (η : ℂ))).re| ≤ B := by
    have hm14 : (m : ℝ) ≤ 14 := by
      have hm' := Finset.mem_range.mp hm
      have hl := degree_upper j
      exact_mod_cast (show m ≤ 14 by omega)
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    apply W_pole_re_bound hη
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_I_re, Complex.ofReal_im]
      nlinarith
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_I_re, Complex.ofReal_im]
      exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩
    · simpa using ht
  unfold F
  rw [Complex.re_sum]
  calc
    _ ≤ ∑ m ∈ Finset.range (Multiplier.length j),
        |((Multiplier.coefficient j m : ℂ) * Kernel.W
          (((((σ - 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I) + ((h * (m : ℝ) : ℝ) : ℂ)) / (η : ℂ))).re| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ m ∈ Finset.range (Multiplier.length j), |Multiplier.coefficient j m| *
        |(Kernel.W (((((σ - 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I) +
          ((h * (m : ℝ) : ℝ) : ℂ)) / (η : ℂ))).re| := by
      apply Finset.sum_congr rfl
      intro m _
      simp [Complex.mul_re, abs_mul]
    _ ≤ ∑ m ∈ Finset.range (Multiplier.length j), |Multiplier.coefficient j m| * B := by
      apply Finset.sum_le_sum
      intro m hm
      exact mul_le_mul_of_nonneg_left (hb m hm) (abs_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; rfl

@[blueprint "varlamov-nonreal-pole"
  (title := "Varlamov, Lemma 7.3: nonreal pole terms")
  (statement := /-- The sum of the nonreal pole terms is at most
  $10^{-10}\eta$. The transform estimate and every numerical condition C9
  are proved in Lean for all seven bands. -/)
  (uses := ["varlamov-transform-left-bound", "varlamov-trigonometric-polynomial"])]
theorem nonreal_pole_bound (j : Fin 7) {σ h η t : ℝ}
    (hη : 0 < η) (hηmax : η ≤ etaMax j) (hσ : 1 - η ≤ σ) (hσ1 : σ ≤ 1)
    (hh : 0 ≤ h) (hh1 : h ≤ 1) (ht : H ≤ |t|) :
    (∑ k ∈ Finset.range 12, Trigonometric.a (k + 1) *
      (F j h η (((σ - 1 : ℝ) : ℂ) + (((k + 1 : ℕ) : ℂ) * (t : ℂ)) * Complex.I)).re) ≤ 1e-10 * η := by
  have hH : (0 : ℝ) < H := by norm_num [H]
  have hη1 : η ≤ 1 := hηmax.trans (by linarith [(etaMax_range j).2])
  let B := Multiplier.coeffNorm j * (140 * η / H ^ 2 + Kernel.Cminus * η ^ 3 / H ^ 3)
  have hB : 0 ≤ B := mul_nonneg (Multiplier.coeffNorm_nonneg j) (by
    have hc := Kernel.Cminus_pos
    have hH : (0 : ℝ) < H := by norm_num [H]
    positivity)
  have hb (k : ℕ) : (F j h η (((σ - 1 : ℝ) : ℂ) + (((k + 1 : ℕ) : ℂ) * (t : ℂ)) * Complex.I)).re ≤ B := by
    have hk : (1 : ℝ) ≤ (k + 1 : ℕ) := by exact_mod_cast (show 1 ≤ k + 1 by omega)
    have hkt : H ≤ |((k + 1 : ℕ) : ℝ) * t| := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (k + 1 : ℕ))]
      nlinarith [abs_nonneg t]
    have h := F_pole_re_bound j hη hσ hσ1 hη1 hh hh1 hkt
    push_cast at h ⊢
    exact (le_abs_self _).trans h
  calc
    _ ≤ ∑ k ∈ Finset.range 12, Trigonometric.a (k + 1) * B := by
      apply Finset.sum_le_sum
      intro k hk
      have hk' : k + 1 < 13 := by have := Finset.mem_range.mp hk; omega
      exact mul_le_mul_of_nonneg_left (hb k) (Trigonometric.a_nonneg ⟨k + 1, hk'⟩)
    _ = (697654317962413463864378 / 200000000000105967340467 : ℝ) * B := by
      rw [← Finset.sum_mul, Trigonometric.a_plus]
    _ ≤ 4 * (10 * (140 * η / H ^ 2 + 1000000 * η / H ^ 3)) := by
      have hη3 : η ^ 3 ≤ η := by nlinarith [sq_nonneg η, mul_nonneg hη.le (show 0 ≤ 1 - η ^ 2 by nlinarith)]
      have hc := Cminus_upper
      have hcn := Kernel.Cminus_pos
      have hcoeff := (coeffNorm_upper j).le
      dsimp [B]
      gcongr ; first | positivity | norm_num
    _ ≤ _ := by norm_num [H]; nlinarith

#print axioms nonreal_pole_bound
end Varlamov
