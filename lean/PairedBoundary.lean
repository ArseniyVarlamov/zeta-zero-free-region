import PrimeNumberTheoremAnd.IEANTN.Varlamov.PairedBoundaryPoint
import PrimeNumberTheoremAnd.IEANTN.Varlamov.PairedTransform
import PrimeNumberTheoremAnd.IEANTN.Varlamov.UnitTransform

namespace Varlamov
open Real
open scoped BigOperators ComplexConjugate

lemma finite_pair_shift (c A : ℕ → ℝ) (n : ℕ) (hc : c n = 0) :
    (∑ m ∈ Finset.range n, c m * A m) + (∑ m ∈ Finset.range n, c m * A (m + 1)) =
      c 0 * A 0 + ∑ m ∈ Finset.range n, (c (m + 1) + c m) * A (m + 1) := by
  have hs := Finset.sum_range_succ' (fun m => c m * A m) n
  rw [Finset.sum_range_succ, hc, zero_mul, add_zero] at hs
  simp_rw [add_mul, Finset.sum_add_distrib]
  linarith

lemma signed_error_lower {x a e c : ℝ} (h : |x - a| ≤ e) : c * a - |c| * e ≤ c * x := by
  have hp : |c * x - c * a| ≤ |c| * e := by
    rw [← mul_sub, abs_mul]
    exact mul_le_mul_of_nonneg_left h (abs_nonneg c)
  have hh := (abs_le.mp hp).1
  linarith

lemma Pi_boundary_sum (j : Fin 7) (h η y : ℝ) :
    Pi j h η ((y : ℂ) * Complex.I) =
      (Kernel.W (((y : ℂ) * Complex.I) / (η : ℂ))).re +
      ∑ m ∈ Finset.range (Multiplier.length j),
        (Multiplier.coefficient j (m + 1) + Multiplier.coefficient j m) *
          (Kernel.W (((((h * ((m + 1 : ℕ) : ℝ) : ℝ) : ℂ)) +
            (y : ℂ) * Complex.I) / (η : ℂ))).re := by
  let A : ℕ → ℝ := fun m =>
    (Kernel.W (((((h * (m : ℝ) : ℝ) : ℂ)) + (y : ℂ) * Complex.I) / (η : ℂ))).re
  have hleft (m : ℕ) :
      (((y : ℂ) * Complex.I) + ((h * (m : ℝ) : ℝ) : ℂ)) / (η : ℂ) =
        (((h * (m : ℝ) : ℝ) : ℂ) + (y : ℂ) * Complex.I) / (η : ℂ) := by congr 1; ring
  have hright (m : ℕ) :
      (((h : ℂ) - conj ((y : ℂ) * Complex.I)) + ((h * (m : ℝ) : ℝ) : ℂ)) / (η : ℂ) =
        (((h * ((m + 1 : ℕ) : ℝ) : ℝ) : ℂ) + (y : ℂ) * Complex.I) / (η : ℂ) := by
    push_cast
    simp
    congr 1
    ring
  unfold Pi F
  simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  simp_rw [hleft, hright]
  have hs := finite_pair_shift (Multiplier.coefficient j) A (Multiplier.length j)
    (Multiplier.coefficient_end j)
  simpa only [A, Multiplier.coefficient_zero, mul_one, one_mul, Nat.cast_zero,
    mul_zero, Complex.ofReal_zero, zero_add] using hs

@[blueprint "varlamov-paired-boundary-positive"
  (title := "Varlamov, Proposition 5.2: boundary of the strip")
  (statement := /-- The paired transform is nonnegative on both vertical edges
  of the strip for every band. The common-denominator error estimate is checked
  for coefficients of either sign. -/)
  (uses := ["varlamov-transform-fourier-positive", "varlamov-transform-right-bound"])]
theorem Pi_boundary_nonneg (j : Fin 7) {h η : ℝ}
    (hh : hMin j ≤ h) (hη : 0 < η) (hηmax : η ≤ etaMax j) (y : ℝ) :
    0 ≤ Pi j h η ((y : ℂ) * Complex.I) := by
  have hh0 : 0 < h := (hMin_pos j).trans_le hh
  let p : ℝ := 10 * η / h
  let Y : ℝ := (y / h) ^ 2
  have hp : 0 < p := by dsimp [p]; positivity
  have hY : 0 ≤ Y := sq_nonneg _
  have hzero : 0 ≤ (Kernel.W (((y : ℂ) * Complex.I) / (η : ℂ))).re := by
    have he : ((y : ℂ) * Complex.I) / (η : ℂ) = ((y / η : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [he]
    exact Kernel.W_imaginary_nonneg (y / η)
  have hterm (m : ℕ) :
      p * (((m + 1 : ℝ) * (Multiplier.coefficient j (m + 1) + Multiplier.coefficient j m) -
        pairedEps j * |Multiplier.coefficient j (m + 1) + Multiplier.coefficient j m| / (m + 1)) /
          ((m + 1 : ℝ) ^ 2 + Y)) ≤
      (Multiplier.coefficient j (m + 1) + Multiplier.coefficient j m) *
        (Kernel.W (((((h * ((m + 1 : ℕ) : ℝ) : ℝ) : ℂ)) +
          (y : ℂ) * Complex.I) / (η : ℂ))).re := by
    have hm : (1 : ℝ) ≤ (m + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
    have he := boundary_point_error j hh hη hηmax (m := ((m + 1 : ℕ) : ℝ)) (y := y) hm
    have hl := signed_error_lower (c := Multiplier.coefficient j (m + 1) + Multiplier.coefficient j m) he
    have hd : 0 < (m + 1 : ℝ) ^ 2 + Y := by positivity
    have hid : (Multiplier.coefficient j (m + 1) + Multiplier.coefficient j m) *
        ((10 * η / h) * (m + 1 : ℕ) / (((m + 1 : ℕ) : ℝ) ^ 2 + (y / h) ^ 2)) -
          |Multiplier.coefficient j (m + 1) + Multiplier.coefficient j m| *
            ((10 * η / h) * pairedEps j / (((m + 1 : ℕ) : ℝ) * (((m + 1 : ℕ) : ℝ) ^ 2 + (y / h) ^ 2))) =
        p * (((m + 1 : ℝ) * (Multiplier.coefficient j (m + 1) + Multiplier.coefficient j m) -
          pairedEps j * |Multiplier.coefficient j (m + 1) + Multiplier.coefficient j m| / (m + 1)) /
            ((m + 1 : ℝ) ^ 2 + Y)) := by
      dsimp [p, Y]
      push_cast
      field_simp
      
    rw [hid] at hl
    exact hl
  have hsum := Finset.sum_le_sum (fun m (_hm : m ∈ Finset.range (Multiplier.length j)) => hterm m)
  rw [← Finset.mul_sum, ← Multiplier.pair_from_coefficients] at hsum
  have hpair : 0 ≤ p * Multiplier.pair j Y := (mul_pos hp (Multiplier.pair_pos j hY)).le
  rw [Pi_boundary_sum]
  exact add_nonneg hzero (hpair.trans hsum)

#print axioms Pi_boundary_nonneg

end Varlamov
