import PrimeNumberTheoremAnd.IEANTN.Varlamov.GammaBounds
import PrimeNumberTheoremAnd.IEANTN.Varlamov.PoleTerms
import PrimeNumberTheoremAnd.IEANTN.Varlamov.KadiriInput
import PrimeNumberTheoremAnd.IEANTN.Varlamov.RemainderLedger

namespace Varlamov
open Real
open scoped BigOperators

noncomputable def gammaX (j : Fin 7) (m : ℕ) : ℝ :=
  if 0 < Multiplier.coefficient j m then (sigmaMax j + (2 * sigmaMax j - 1) * (m : ℝ)) / 2 + 1
  else (sigmaMin j + hMin j * (m : ℝ)) / 2 + 1
noncomputable def gammaLogMoment : ℝ :=
  ∑ k ∈ Finset.range 12, Trigonometric.a (k + 1) * Real.log ((k + 1 : ℕ) : ℝ)
noncomputable def gammaG (j : Fin 7) : ℝ := -(
  (1 / 2) * (∑ m ∈ Finset.range (Multiplier.length j), Multiplier.coefficient j m * realDigamma (gammaX j m)) -
  (Multiplier.kappa j 1 / 2) * Real.log Real.pi + (Multiplier.kappa j 1 / 2) * gammaLogMoment -
  (aPlus * Multiplier.kappa j 1 / 2) * Real.log (2 * Real.pi) +
  (aPlus * Multiplier.coeffNorm j / 2) * 1e-10)
noncomputable def gammaQ (j : Fin 7) : ℝ := aPlus * Multiplier.kappa j 1 * 10 / 2

lemma coefficient_sum (j : Fin 7) :
    (∑ m ∈ Finset.range (Multiplier.length j), Multiplier.coefficient j m) = Multiplier.kappa j 1 := by
  simpa only [one_pow, mul_one] using (Multiplier.kappa_sum j 1).symm

lemma gammaX_pos (j : Fin 7) (m : ℕ) (hσMax : sigmaMin j ≤ sigmaMax j) : 0 < gammaX j m := by
  have hσ := (sigmaMin_range j).1
  have hh := hMin_pos j
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  unfold gammaX
  split_ifs <;> nlinarith

lemma real_gamma_coefficient_bound (j : Fin 7) {σ h : ℝ}
    (hσ : sigmaMin j ≤ σ) (hσmax : σ ≤ sigmaMax j)
    (hh : hMin j ≤ h) (hhmax : h ≤ 2 * sigmaMax j - 1) (m : ℕ) :
    Multiplier.coefficient j m * gammaTerm (((σ + h * (m : ℝ) : ℝ) : ℂ)) ≤
      Multiplier.coefficient j m * (-(1 / 2) * Real.log Real.pi + (1 / 2) * realDigamma (gammaX j m)) := by
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hx : 0 < (σ + h * (m : ℝ)) / 2 + 1 := by nlinarith [(sigmaMin_range j).1, hMin_pos j]
  have hxg := gammaX_pos j m (hσ.trans hσmax)
  have harg : ((((σ + h * (m : ℝ) : ℝ) : ℂ)) / 2 + 1) = ((((σ + h * (m : ℝ)) / 2 + 1 : ℝ) : ℂ)) := by push_cast; rfl
  unfold gammaTerm
  rw [harg]
  change _ * (-(1 / 2) * Real.log Real.pi + (1 / 2) * realDigamma ((σ + h * (m : ℝ)) / 2 + 1)) ≤ _
  by_cases hc : 0 < Multiplier.coefficient j m
  · have hxx : (σ + h * (m : ℝ)) / 2 + 1 ≤ gammaX j m := by
      simp only [gammaX, ite_eq_left hc]
      nlinarith
    have hp := realDigamma_monotoneOn hx hxg hxx
    exact mul_le_mul_of_nonneg_left (by linarith) hc.le
  · have hxx : gammaX j m ≤ (σ + h * (m : ℝ)) / 2 + 1 := by
      simp only [gammaX, ite_eq_right hc]
      nlinarith
    have hp := realDigamma_monotoneOn hxg hx hxx
    exact mul_le_mul_of_nonpos_left (by linarith) (le_of_not_gt hc)

lemma nonreal_gamma_coefficient_bound (hK3 : KadiriDigammaInput) (j : Fin 7) {σ h t : ℝ}
    (hσ : sigmaMin j ≤ σ) (hσ1 : σ ≤ 1) (hh : hMin j ≤ h) (hh1 : h ≤ 1)
    (ht : H ≤ |t|) {m : ℕ} (hm : m ∈ Finset.range (Multiplier.length j)) (k : ℕ) :
    Multiplier.coefficient j m * gammaTerm
      ((((σ + h * (m : ℝ) : ℝ) : ℂ) + ((k + 1 : ℕ) : ℂ) * (t : ℂ) * Complex.I)) ≤
      Multiplier.coefficient j m / 2 * (Real.log |t| + Real.log ((k + 1 : ℕ) : ℝ) - Real.log (2 * Real.pi)) +
        |Multiplier.coefficient j m| / 2 * 1e-10 := by
  let x : ℝ := (σ + h * (m : ℝ)) / 2 + 1
  let y : ℝ := ((k + 1 : ℕ) : ℝ) * t / 2
  have hH : (0 : ℝ) < H := by norm_num [H]
  have ht0 : 0 < |t| := hH.trans_le ht
  have hk : (1 : ℝ) ≤ (k + 1 : ℕ) := by exact_mod_cast (show 1 ≤ k + 1 by omega)
  have hk0 : (0 : ℝ) < (k + 1 : ℕ) := by linarith
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hm14 : (m : ℝ) ≤ 14 := by
    have := Finset.mem_range.mp hm
    have := degree_upper j
    exact_mod_cast (show m ≤ 14 by omega)
  have hx : 1 ≤ x := by dsimp [x]; nlinarith [(sigmaMin_range j).1, hMin_pos j]
  have hx9 : x ≤ 9 := by dsimp [x]; nlinarith
  have hy : H / 2 ≤ |y| := by
    dsimp [y]
    rw [abs_div, abs_mul, abs_of_pos hk0]
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith
  have he := (digamma_high_error hK3 hx hx9 hy).le
  let p := (Complex.digamma ((x : ℂ) + (y : ℂ) * Complex.I)).re
  let c := Multiplier.coefficient j m
  have hp : c * p ≤ c * Real.log |y| + |c| * 1e-10 := by
    have he' : |c * (p - Real.log |y|)| ≤ |c| * 1e-10 := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left he (abs_nonneg c)
    have hl := le_abs_self (c * (p - Real.log |y|))
    nlinarith
  have hlog : Real.log |y| = Real.log |t| + Real.log ((k + 1 : ℕ) : ℝ) - Real.log 2 := by
    dsimp [y]
    rw [abs_div, abs_mul, abs_of_pos hk0, abs_of_pos (by norm_num : (0 : ℝ) < 2),
      Real.log_div (ne_of_gt (mul_pos hk0 ht0)) (by norm_num), Real.log_mul (ne_of_gt hk0) (ne_of_gt ht0)]
    ring
  have hlogpi : Real.log (2 * Real.pi) = Real.log 2 + Real.log Real.pi :=
    Real.log_mul (by norm_num) (ne_of_gt Real.pi_pos)
  have harg : (((((σ + h * (m : ℝ) : ℝ) : ℂ) + ((k + 1 : ℕ) : ℂ) * (t : ℂ) * Complex.I)) / 2 + 1) =
      ((x : ℂ) + (y : ℂ) * Complex.I) := by
    dsimp [x, y]
    push_cast
    ring
  unfold gammaTerm
  rw [harg, hlogpi]
  rw [hlog] at hp
  change _ ≤ _ at hp
  dsimp only [c, p] at hp
  nlinarith

lemma sum_affine (N : ℕ) (a b : ℝ) (f g : ℕ → ℝ) :
    (∑ k ∈ Finset.range N, f k * (a + b * g k)) =
      a * (∑ k ∈ Finset.range N, f k) + b * (∑ k ∈ Finset.range N, f k * g k) := by
  calc
    _ = ∑ k ∈ Finset.range N, (a * f k + b * (f k * g k)) := by
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

@[blueprint "varlamov-gamma-factor"
  (title := "Varlamov, Lemma 7.2: gamma factor")
  (statement := /-- The gamma contribution is at most $QA-Gw_0\eta$.
  Kadiri's published digamma error is an explicit premise. Real digamma
  monotonicity, sign-dependent endpoint choices and the finite ledger are
  proved in Lean. Positivity of the particular numerical G is a separate
  remaining certificate obligation. -/)
  (uses := ["varlamov-digamma-growth", "varlamov-trigonometric-polynomial"])]
theorem gamma_factor_bound (hK3 : KadiriDigammaInput) (j : Fin 7) {σ h η t A : ℝ}
    (hσ : sigmaMin j ≤ σ) (hσmax : σ ≤ sigmaMax j) (hσ1 : σ ≤ 1)
    (hh : hMin j ≤ h) (hh1 : h ≤ 1) (hhmax : h ≤ 2 * sigmaMax j - 1) (hη : 0 < η) (ht : H ≤ |t|)
    (hA : η * Real.log |t| = A) :
    η * 10 * (∑ k ∈ Finset.range 13, Trigonometric.a k *
      (∑ m ∈ Finset.range (Multiplier.length j), Multiplier.coefficient j m *
        gammaTerm ((((σ + h * (m : ℝ) : ℝ) : ℂ) + (k : ℂ) * (t : ℂ) * Complex.I)))) ≤
      gammaQ j * A - gammaG j * 10 * η := by
  let B0 := (1 / 2) * (∑ m ∈ Finset.range (Multiplier.length j), Multiplier.coefficient j m * realDigamma (gammaX j m)) -
    (Multiplier.kappa j 1 / 2) * Real.log Real.pi
  let B := (Multiplier.kappa j 1 / 2) * (Real.log |t|-Real.log (2 * Real.pi)) + Multiplier.coeffNorm j / 2 * 1e-10
  have hzero : (∑ m ∈ Finset.range (Multiplier.length j), Multiplier.coefficient j m *
      gammaTerm (((σ + h * (m : ℝ) : ℝ) : ℂ))) ≤ B0 := by
    calc
      _ ≤ ∑ m ∈ Finset.range (Multiplier.length j), Multiplier.coefficient j m *
          (-(1 / 2) * Real.log Real.pi + (1 / 2) * realDigamma (gammaX j m)) :=
        Finset.sum_le_sum (fun m _ => real_gamma_coefficient_bound j hσ hσmax hh hhmax m)
      _ = _ := by
        dsimp [B0]
        rw [sum_affine, coefficient_sum]
        ring
  have hnonreal (k : ℕ) : (∑ m ∈ Finset.range (Multiplier.length j), Multiplier.coefficient j m *
      gammaTerm ((((σ + h * (m : ℝ) : ℝ) : ℂ) + ((k + 1 : ℕ) : ℂ) * (t : ℂ) * Complex.I))) ≤
      B + (Multiplier.kappa j 1 / 2) * Real.log ((k + 1 : ℕ) : ℝ) := by
    calc
      _ ≤ ∑ m ∈ Finset.range (Multiplier.length j),
          (Multiplier.coefficient j m / 2 * (Real.log |t| + Real.log ((k + 1 : ℕ) : ℝ) - Real.log (2 * Real.pi)) +
            |Multiplier.coefficient j m| / 2 * 1e-10) :=
        Finset.sum_le_sum (fun m hm => nonreal_gamma_coefficient_bound hK3 j hσ hσ1 hh hh1 ht hm k)
      _ = _ := by
        rw [Finset.sum_add_distrib]
        have he1 : (∑ m ∈ Finset.range (Multiplier.length j), Multiplier.coefficient j m / 2 *
            (Real.log |t| + Real.log ((k + 1 : ℕ) : ℝ) - Real.log (2 * Real.pi))) =
            (Multiplier.kappa j 1 / 2) * (Real.log |t| + Real.log ((k + 1 : ℕ) : ℝ) - Real.log (2 * Real.pi)) := by
          simp_rw [div_mul_eq_mul_div, div_eq_mul_inv, mul_assoc]
          rw [← Finset.sum_mul, coefficient_sum]
        have he2 : (∑ m ∈ Finset.range (Multiplier.length j), |Multiplier.coefficient j m| / 2 * 1e-10) =
            Multiplier.coeffNorm j / 2 * 1e-10 := by rw [← Finset.sum_mul, ← Finset.sum_div]; rfl
        rw [he1, he2]
        dsimp [B]
        ring
  have htotal : (∑ k ∈ Finset.range 13, Trigonometric.a k *
      (∑ m ∈ Finset.range (Multiplier.length j), Multiplier.coefficient j m *
        gammaTerm ((((σ + h * (m : ℝ) : ℝ) : ℂ) + (k : ℂ) * (t : ℂ) * Complex.I)))) ≤
      aPlus * Multiplier.kappa j 1 / 2 * Real.log |t|-gammaG j := by
    rw [show (13 : ℕ) = 12 + 1 from rfl, Finset.sum_range_succ']
    have ha0 : Trigonometric.a 0 = 1 := by norm_num [Trigonometric.a]
    simp only [Nat.cast_zero, zero_mul, add_zero, ha0, one_mul]
    calc
      _ ≤ (∑ k ∈ Finset.range 12, Trigonometric.a (k + 1) *
          (B + (Multiplier.kappa j 1 / 2) * Real.log ((k + 1 : ℕ) : ℝ))) + B0 := by
        apply add_le_add _ hzero
        apply Finset.sum_le_sum
        intro k hk
        have hk' : k + 1 < 13 := by have := Finset.mem_range.mp hk; omega
        exact mul_le_mul_of_nonneg_left (hnonreal k) (Trigonometric.a_nonneg ⟨k + 1, hk'⟩)
      _ = _ := by
        rw [sum_affine, Trigonometric.a_plus]
        dsimp [B, B0, gammaG, gammaLogMoment, aPlus]
        ring
  calc
    _ ≤ η * 10 * (aPlus * Multiplier.kappa j 1 / 2 * Real.log |t|-gammaG j) :=
      mul_le_mul_of_nonneg_left htotal (by positivity)
    _ = _ := by rw [← hA]; unfold gammaQ; ring

#print axioms gamma_factor_bound
end Varlamov
