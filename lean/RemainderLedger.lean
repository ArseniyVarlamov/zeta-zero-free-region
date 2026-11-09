import PrimeNumberTheoremAnd.IEANTN.Varlamov.NonrealSeries
import PrimeNumberTheoremAnd.IEANTN.Varlamov.PairedPositivity
import PrimeNumberTheoremAnd.IEANTN.Varlamov.Trigonometric

namespace Varlamov
open Real
open scoped BigOperators

noncomputable def aPlus : ℝ := 697654317962413463864378 / 200000000000105967340467
noncomputable def remainderU (j : Fin 7) (m : ℕ) : ℝ := sigmaMin j + hMin j * m + 2
noncomputable def remainderC (j : Fin 7) (m : ℕ) : ℝ := Kernel.C (remainderU j m / etaMax j)
noncomputable def remainderE (j : Fin 7) : ℝ :=
  ∑ m ∈ Finset.range (Multiplier.length j), |Multiplier.coefficient j m| * remainderC j m *
    (1 / (remainderU j m) ^ 3 + 1 / (4 * (remainderU j m) ^ 2) + aPlus * (1 / H ^ 3 + 1 / (2 * H ^ 2)))

lemma remainderU_pos (j : Fin 7) (m : ℕ) : 0 < remainderU j m := by
  have hσ := (sigmaMin_range j).1
  have hh := hMin_pos j
  have hn : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  unfold remainderU
  nlinarith

lemma remainderE_pos (j : Fin 7) : 0 < remainderE j := by
  unfold remainderE
  apply Finset.sum_pos'
  · intro m _
    have hu := remainderU_pos j m
    have hc := Kernel.C_pos (div_pos hu (etaMax_range j).1)
    have hH : (0 : ℝ) < H := by norm_num [H]
    have ha : (0 : ℝ) < aPlus := by norm_num [aPlus]
    dsimp only [remainderC]
    positivity
  · refine ⟨0, Finset.mem_range.mpr (Multiplier.length_pos j), ?_⟩
    rw [Multiplier.coefficient_zero, abs_one, one_mul]
    have hu := remainderU_pos j 0
    have hc := Kernel.C_pos (div_pos hu (etaMax_range j).1)
    have hH : (0 : ℝ) < H := by norm_num [H]
    have ha : (0 : ℝ) < aPlus := by norm_num [aPlus]
    dsimp only [remainderC]
    positivity

lemma remainder_one_shift (hC : HalfPlaneCauchyInput) (j : Fin 7) {σ h η t : ℝ}
    (hσ : sigmaMin j ≤ σ) (hh : hMin j ≤ h) (hη : 0 < η)
    (hηmax : η ≤ etaMax j) (ht : H ≤ |t|) (m : ℕ) :
    (∑ k ∈ Finset.range 13, Trigonometric.a k *
      ‖Kernel.Delta η ((((σ + h * (m : ℝ) : ℝ) : ℂ) + (k : ℂ) * (t : ℂ) * Complex.I))‖) ≤
      remainderC j m * η ^ 3 * (1 / (remainderU j m) ^ 3 + 1 / (4 * (remainderU j m) ^ 2) +
        aPlus * (1 / H ^ 3 + 1 / (2 * H ^ 2))) := by
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hh0 : 0 < h := (hMin_pos j).trans_le hh
  have hs : (1 / 2 : ℝ) < σ + h * (m : ℝ) := by
    nlinarith [(sigmaMin_range j).1]
  have hu := remainderU_pos j m
  have hsu : remainderU j m ≤ σ + h * (m : ℝ) + 2 := by
    unfold remainderU
    nlinarith
  have hH : (0 : ℝ) < H := by norm_num [H]
  have hbound (k : ℕ) : ‖Kernel.Delta η
      ((((σ + h * (m : ℝ) : ℝ) : ℂ) + ((k + 1 : ℕ) : ℂ) * (t : ℂ) * Complex.I))‖ ≤
      remainderC j m * η ^ 3 * (1 / H ^ 3 + 1 / (2 * H ^ 2)) := by
    apply Kernel.Delta_height_bound hC hη hηmax
    · simpa using hs
    · exact hu
    · simpa using hsu
    · exact hH
    · have hk : (1 : ℝ) ≤ (k + 1 : ℕ) := by exact_mod_cast (show 1 ≤ k + 1 by omega)
      have he : |((((σ + h * (m : ℝ) : ℝ) : ℂ) + ((k + 1 : ℕ) : ℂ) * (t : ℂ) * Complex.I)).im| =
          ((k + 1 : ℕ) : ℝ) * |t| := by simp [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ (k : ℝ) + 1 by positivity)]
      rw [he]
      nlinarith [abs_nonneg t]
  have hzero : ‖Kernel.Delta η (((σ + h * (m : ℝ) : ℝ) : ℂ))‖ ≤
      remainderC j m * η ^ 3 * (1 / (remainderU j m) ^ 3 + 1 / (4 * (remainderU j m) ^ 2)) := by
    exact Kernel.Delta_real_bound hC hη hηmax (by simpa using hs) hu (by simpa using hsu)
  rw [show (13 : ℕ) = 12 + 1 from rfl, Finset.sum_range_succ']
  have ha0 : Trigonometric.a 0 = 1 := by norm_num [Trigonometric.a]
  simp only [Nat.cast_zero, zero_mul, add_zero, ha0, one_mul]
  have hpositive : (∑ k ∈ Finset.range 12, Trigonometric.a (k + 1) *
      ‖Kernel.Delta η ((((σ + h * (m : ℝ) : ℝ) : ℂ) + ((k + 1 : ℕ) : ℂ) * (t : ℂ) * Complex.I))‖) ≤
      aPlus * (remainderC j m * η ^ 3 * (1 / H ^ 3 + 1 / (2 * H ^ 2))) := by
    calc
      _ ≤ ∑ k ∈ Finset.range 12, Trigonometric.a (k + 1) *
          (remainderC j m * η ^ 3 * (1 / H ^ 3 + 1 / (2 * H ^ 2))) := by
        apply Finset.sum_le_sum
        intro k hk
        have hk' : k + 1 < 13 := by have := Finset.mem_range.mp hk; omega
        exact mul_le_mul_of_nonneg_left (hbound k) (Trigonometric.a_nonneg ⟨k + 1, hk'⟩)
      _ = _ := by rw [← Finset.sum_mul, Trigonometric.a_plus]; rfl
  calc
    _ ≤ aPlus * (remainderC j m * η ^ 3 * (1 / H ^ 3 + 1 / (2 * H ^ 2))) +
        remainderC j m * η ^ 3 * (1 / (remainderU j m) ^ 3 + 1 / (4 * (remainderU j m) ^ 2)) :=
      add_le_add hpositive hzero
    _ = _ := by ring

@[blueprint "varlamov-remainder-bound"
  (title := "Varlamov, Lemma 6.4: aggregate remainder bound")
  (statement := /-- The sum of the absolute remainders over every trigonometric
  frequency and multiplier shift is at most $E\eta^3$, with exactly the E
  of the article. The sole external input in this block is the classical
  half-plane Cauchy formula used for Proposition 6.3. -/)
  (uses := ["varlamov-trivial-zero-remainder", "varlamov-transform-right-bound"])]
theorem remainder_bound (hC : HalfPlaneCauchyInput) (j : Fin 7) {σ h η t : ℝ}
    (hσ : sigmaMin j ≤ σ) (hh : hMin j ≤ h) (hη : 0 < η)
    (hηmax : η ≤ etaMax j) (ht : H ≤ |t|) :
    (∑ k ∈ Finset.range 13, Trigonometric.a k *
      (∑ m ∈ Finset.range (Multiplier.length j), |Multiplier.coefficient j m| *
        ‖Kernel.Delta η ((((σ + h * (m : ℝ) : ℝ) : ℂ) + (k : ℂ) * (t : ℂ) * Complex.I))‖)) ≤
      remainderE j * η ^ 3 := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ m ∈ Finset.range (Multiplier.length j), |Multiplier.coefficient j m| *
        (∑ k ∈ Finset.range 13, Trigonometric.a k *
          ‖Kernel.Delta η ((((σ + h * (m : ℝ) : ℝ) : ℂ) + (k : ℂ) * (t : ℂ) * Complex.I))‖) := by
      apply Finset.sum_congr rfl
      intro m _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ ≤ ∑ m ∈ Finset.range (Multiplier.length j), |Multiplier.coefficient j m| *
        (remainderC j m * η ^ 3 * (1 / (remainderU j m) ^ 3 + 1 / (4 * (remainderU j m) ^ 2) +
          aPlus * (1 / H ^ 3 + 1 / (2 * H ^ 2)))) := by
      apply Finset.sum_le_sum
      intro m _
      exact mul_le_mul_of_nonneg_left (remainder_one_shift hC j hσ hh hη hηmax ht m) (abs_nonneg _)
    _ = _ := by
      unfold remainderE
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro m _
      ring

#print axioms remainder_bound
end Varlamov
