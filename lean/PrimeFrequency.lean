import PrimeNumberTheoremAnd.IEANTN.Varlamov.PrimeLower

namespace Varlamov
open Real
open scoped BigOperators

lemma primeTerm_real_part (f : ℝ → ℝ) (σ t : ℝ) (k n : ℕ) :
    (primeTerm f ((σ : ℂ) + (k : ℂ) * (t : ℂ) * Complex.I) n).re =
      ArithmeticFunction.vonMangoldt n * Real.exp (-σ * Real.log n) * f (Real.log n) *
        Real.cos ((k : ℝ) * (t * Real.log n)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [primeTerm]
  · have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
    unfold primeTerm
    rw [Complex.cpow_def_of_ne_zero hnC, div_eq_mul_inv, ← Complex.exp_neg]
    have he : -(Complex.log (n : ℂ) * ((σ : ℂ) + (k : ℂ) * (t : ℂ) * Complex.I)) =
        (((-σ * Real.log n : ℝ) : ℂ)) + (((-((k : ℝ) * (t * Real.log n)) : ℝ) : ℂ)) * Complex.I := by
      rw [← Complex.natCast_log]
      push_cast
      ring
    rw [he]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero, Complex.I_re, Complex.exp_re, Complex.add_re, Complex.add_im, Complex.mul_I_re,
      Complex.mul_I_im, Complex.neg_re, Complex.neg_im, add_zero, zero_add,
      Real.cos_neg]
    ring

@[blueprint "varlamov-prime-frequency-bridge"
  (title := "Varlamov, Proposition 8.1: frequency-sum identity")
  (statement := /-- The sum of the explicit-formula left sides with the
  trigonometric coefficients equals the actual real prime contribution
  containing P(t log n). The exchanges are justified by finite support. -/)
  (uses := ["varlamov-explicit-formula", "varlamov-trigonometric-polynomial"])]
theorem prime_frequency_sum (j : Fin 7) {η : ℝ} (hη : 0 < η) (σ h t : ℝ) :
    (∑ k ∈ Finset.range 13, Trigonometric.a k *
      primeSum (testFunction j h η) ((σ : ℂ) + (k : ℂ) * (t : ℂ) * Complex.I)) =
      ∑' n : ℕ, primeContribution j σ h η t n := by
  let f : ℕ → ℕ → ℂ := fun k n => (Trigonometric.a k : ℂ) *
    primeTerm (testFunction j h η) ((σ : ℂ) + (k : ℂ) * (t : ℂ) * Complex.I) n
  have hp (k : ℕ) : Summable (primeTerm (testFunction j h η)
      ((σ : ℂ) + (k : ℂ) * (t : ℂ) * Complex.I)) :=
    primeTerm_summable (D := Kernel.d / η) (fun u hu => testFunction_zero_after j hη h hu) _
  have hf (k : ℕ) : Summable (f k) := (hp k).mul_left _
  have hfs : Summable (fun n : ℕ => ∑ k ∈ Finset.range 13, f k n) :=
    summable_sum (fun k _ => hf k)
  have hRe : (∑ k ∈ Finset.range 13, ∑' n : ℕ, f k n).re =
      ∑ k ∈ Finset.range 13, Trigonometric.a k *
        primeSum (testFunction j h η) ((σ : ℂ) + (k : ℂ) * (t : ℂ) * Complex.I) := by
    simp only [f, tsum_mul_left, Complex.re_sum, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, primeSum]
  rw [← hRe, ← Summable.tsum_finsetSum (fun k _ => hf k), Complex.re_tsum hfs]
  apply tsum_congr
  intro n
  simp only [Complex.re_sum, f, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, primeTerm_real_part]
  unfold primeContribution Trigonometric.P
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

#print axioms prime_frequency_sum
end Varlamov
