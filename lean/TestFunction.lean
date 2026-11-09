import PrimeNumberTheoremAnd.IEANTN.Varlamov.KadiriInput
import PrimeNumberTheoremAnd.IEANTN.Varlamov.PairedTransform

namespace Varlamov
open Real MeasureTheory
open scoped BigOperators

noncomputable def shiftedKernel (η h : ℝ) (m : ℕ) (u : ℝ) : ℝ :=
  Real.exp (-(h * (m : ℝ)) * u) * Kernel.smoothKernel η u
noncomputable def testFunction (j : Fin 7) (h η : ℝ) (u : ℝ) : ℝ :=
  Kernel.smoothKernel η u * Multiplier.kappa j (Real.exp (-h * u))

lemma testFunction_sum (j : Fin 7) (h η u : ℝ) : testFunction j h η u =
    ∑ m ∈ Finset.range (Multiplier.length j), Multiplier.coefficient j m * shiftedKernel η h m u := by
  unfold testFunction shiftedKernel
  rw [Multiplier.kappa_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  have he : (Real.exp (-h * u)) ^ m = Real.exp (-(h * (m : ℝ)) * u) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [he]
  ring

lemma testFunction_eq_article (j : Fin 7) {η : ℝ} (hη : 0 < η) (h : ℝ) {u : ℝ} (hu : 0 ≤ u) :
    testFunction j h η u = Kernel.g η u * Multiplier.kappa j (Real.exp (-h * u)) := by
  rw [testFunction, Kernel.smoothKernel_eq_g hη hu]

lemma primeTerm_summable {f : ℝ → ℝ} {D : ℝ}
    (hz : ∀ u : ℝ, D < u → f u = 0) (s : ℂ) : Summable (primeTerm f s) := by
  apply summable_of_hasFiniteSupport
  apply Set.Finite.subset (Set.finite_Iic ⌊Real.exp D⌋₊)
  intro n hn
  have hf : f (Real.log n) ≠ 0 := by
    intro h
    exact hn (by simp [primeTerm, h])
  have hl : Real.log n ≤ D := by
    by_contra h
    exact hf (hz _ (lt_of_not_ge h))
  rw [Set.mem_Iic]
  apply Nat.le_floor
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · exact_mod_cast (Real.exp_pos D).le
  · rw [← Real.exp_log (Nat.cast_pos.mpr hn0), Real.exp_le_exp]
    exact hl

lemma shifted_primeTerm (η h : ℝ) (m : ℕ) (s : ℂ) (n : ℕ) :
    primeTerm (shiftedKernel η h m) s n =
      primeTerm (Kernel.smoothKernel η) (s + ((h * (m : ℝ) : ℝ) : ℂ)) n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [primeTerm]
  · have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
    simp only [primeTerm, shiftedKernel, Complex.cpow_def_of_ne_zero hnC,
      ← Complex.natCast_log, Complex.ofReal_mul, Complex.ofReal_exp]
    have he : Complex.exp (((Real.log n : ℝ) : ℂ) * (s + ((h * (m : ℝ) : ℝ) : ℂ))) =
        Complex.exp (((Real.log n : ℝ) : ℂ) * s) *
          Complex.exp (((h * (m : ℝ) : ℝ) : ℂ) * ((Real.log n : ℝ) : ℂ)) := by
      rw [show (((Real.log n : ℝ) : ℂ) * (s + ((h * (m : ℝ) : ℝ) : ℂ))) =
        (((Real.log n : ℝ) : ℂ) * s) + (((h * (m : ℝ) : ℝ) : ℂ) * ((Real.log n : ℝ) : ℂ)) from by ring,
        Complex.exp_add]
    push_cast at he ⊢
    rw [he]
    rw [neg_mul, Complex.exp_neg]
    field_simp

lemma primeSum_testFunction (j : Fin 7) {η : ℝ} (hη : 0 < η) (h : ℝ) (s : ℂ) :
    primeSum (testFunction j h η) s =
      ∑ m ∈ Finset.range (Multiplier.length j), Multiplier.coefficient j m *
        primeSum (Kernel.smoothKernel η) (s + ((h * (m : ℝ) : ℝ) : ℂ)) := by
  have hp (m : ℕ) : Summable (primeTerm (Kernel.smoothKernel η) (s + ((h * (m : ℝ) : ℝ) : ℂ))) :=
    primeTerm_summable (D := Kernel.d / η) (fun u hu => Kernel.smoothDerivative_zero_of_gt 0 hη hu) _
  have he (n : ℕ) : primeTerm (testFunction j h η) s n =
      ∑ m ∈ Finset.range (Multiplier.length j), (Multiplier.coefficient j m : ℂ) *
        primeTerm (Kernel.smoothKernel η) (s + ((h * (m : ℝ) : ℝ) : ℂ)) n := by
    simp only [primeTerm, testFunction_sum]
    push_cast
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    have hshift := shifted_primeTerm η h m s n
    unfold primeTerm at hshift
    push_cast at hshift
    rw [← hshift]
    ring
  unfold primeSum
  rw [tsum_congr he, Summable.tsum_finsetSum (fun m _ => (hp m).mul_left _)]
  simp only [tsum_mul_left, Complex.re_sum, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]

#print axioms primeSum_testFunction
end Varlamov
