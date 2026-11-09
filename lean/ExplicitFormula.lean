import PrimeNumberTheoremAnd.IEANTN.Varlamov.TestFunction

namespace Varlamov
open Real
open scoped BigOperators

lemma F_re_shift_sum (j : Fin 7) (h η : ℝ) (s v : ℂ) :
    (F j h η (s - v)).re = ∑ m ∈ Finset.range (Multiplier.length j),
      Multiplier.coefficient j m * (Kernel.W ((s + ((h * (m : ℝ) : ℝ) : ℂ) - v) / (η : ℂ))).re := by
  simp only [F, Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  apply Finset.sum_congr rfl
  intro m _
  rw [show s - v + ((h * (m : ℝ) : ℝ) : ℂ) = s + ((h * (m : ℝ) : ℝ) : ℂ) - v from by ring]

lemma zeroes_sum_F (hK2 : KadiriExplicitInput) (j : Fin 7) {h η : ℝ} {s : ℂ}
    (hh : 0 ≤ h) (hη : 0 < η) (hs : (1 / 2 : ℝ) < s.re) :
    riemannZeta.zeroes_sum (Set.Ioo 0 1) Set.univ (fun ρ => (F j h η (s - ρ)).re) =
      ∑ m ∈ Finset.range (Multiplier.length j), Multiplier.coefficient j m *
        riemannZeta.zeroes_sum (Set.Ioo 0 1) Set.univ
          (fun ρ => (Kernel.W ((s + ((h * (m : ℝ) : ℝ) : ℂ) - ρ) / (η : ℂ))).re) := by
  have hsum (m : ℕ) : Summable (fun ρ : riemannZeta.zeroes_rect (Set.Ioo 0 1) Set.univ =>
      (Kernel.W ((s + ((h * (m : ℝ) : ℝ) : ℂ) - (ρ : ℂ)) / (η : ℂ))).re *
        (riemannZeta.order (ρ : ℂ) : ℝ)) := by
    apply (Kernel.scaled_explicit_formula hK2 hη ?_).1
    simp only [Complex.add_re, Complex.ofReal_re]
    nlinarith [Nat.cast_nonneg (α := ℝ) m]
  unfold riemannZeta.zeroes_sum
  simp_rw [F_re_shift_sum, Finset.sum_mul, mul_assoc]
  rw [Summable.tsum_finsetSum (fun m _ => (hsum m).mul_left (Multiplier.coefficient j m))]
  simp only [tsum_mul_left]

@[blueprint "varlamov-explicit-formula"
  (title := "Varlamov, Lemma 6.1: explicit formula for f")
  (statement := /-- For every $\Re s>1/2$, the actual test function f has
  the explicit formula with F and Delta of the article. The only premise
  is the named published Kadiri Proposition 2.1. All rescaling, second-derivative
  integration by parts, finite prime sums and multiplicity-preserving exchanges
  of the zero sums are proved here. -/)
  (uses := ["varlamov-scaled-explicit-formula", "varlamov-test-kernel-admissible"])]
theorem explicit_formula (hK2 : KadiriExplicitInput) (j : Fin 7) {h η : ℝ} {s : ℂ}
    (hh : 0 ≤ h) (hη : 0 < η) (hs : (1 / 2 : ℝ) < s.re) :
    primeSum (testFunction j h η) s =
      η * 10 * (∑ m ∈ Finset.range (Multiplier.length j), Multiplier.coefficient j m *
        gammaTerm (s + ((h * (m : ℝ) : ℝ) : ℂ))) +
      (F j h η (s - 1)).re -
      riemannZeta.zeroes_sum (Set.Ioo 0 1) Set.univ (fun ρ => (F j h η (s - ρ)).re) +
      (∑ m ∈ Finset.range (Multiplier.length j), Multiplier.coefficient j m *
        (Kernel.Delta η (s + ((h * (m : ℝ) : ℝ) : ℂ))).re) := by
  rw [primeSum_testFunction j hη h s, F_re_shift_sum, zeroes_sum_F hK2 j hh hη hs]
  have hform (m : ℕ) : primeSum (Kernel.smoothKernel η) (s + ((h * (m : ℝ) : ℝ) : ℂ)) =
      10 * η * gammaTerm (s + ((h * (m : ℝ) : ℝ) : ℂ)) +
      (Kernel.W ((s + ((h * (m : ℝ) : ℝ) : ℂ) - 1) / (η : ℂ))).re -
      riemannZeta.zeroes_sum (Set.Ioo 0 1) Set.univ
        (fun ρ => (Kernel.W ((s + ((h * (m : ℝ) : ℝ) : ℂ) - ρ) / (η : ℂ))).re) +
      (Kernel.Delta η (s + ((h * (m : ℝ) : ℝ) : ℂ))).re := by
    apply (Kernel.scaled_explicit_formula hK2 hη ?_).2
    simp only [Complex.add_re, Complex.ofReal_re]
    nlinarith [Nat.cast_nonneg (α := ℝ) m]
  simp_rw [hform, mul_add, mul_sub, mul_add]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  congr 3
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  ring

#print axioms explicit_formula
end Varlamov
