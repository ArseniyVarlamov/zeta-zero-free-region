import PrimeNumberTheoremAnd.IEANTN.Varlamov.SmallArguments
import PrimeNumberTheoremAnd.IEANTN.Varlamov.PairedTransform

namespace Varlamov
open Real
open scoped BigOperators

noncomputable def argumentOne (μ η : ℝ) (m : ℕ) : ℝ :=
  ((m : ℝ) + 1) / η - (2 * (m : ℝ) + 1) * μ - 1
noncomputable def argumentTwo (μ η : ℝ) (m : ℕ) : ℝ :=
  (m : ℝ) / η - (2 * (m : ℝ) + 1) * μ + 1
noncomputable def argumentThree (μ η : ℝ) (m : ℕ) : ℝ :=
  (m : ℝ) / η - (2 * (m : ℝ) + 1) * μ

noncomputable def zeroPairTerm (j : Fin 7) (μ η : ℝ) : ℝ :=
  Trigonometric.a 1 * ((F j (1 - 2 * μ * η) η (((1 - μ * η - 1 + η : ℝ)) : ℂ)).re +
    (F j (1 - 2 * μ * η) η (((1 - μ * η - η : ℝ)) : ℂ)).re) -
    (F j (1 - 2 * μ * η) η (((1 - μ * η - 1 : ℝ)) : ℂ)).re

lemma F_real_sum (j : Fin 7) (h η x : ℝ) :
    (F j h η (x : ℂ)).re = ∑ m ∈ Finset.range (Multiplier.length j),
      Multiplier.coefficient j m * realW ((x + h * (m : ℝ)) / η) := by
  simp only [F, ← Complex.ofReal_add, ← Complex.ofReal_div, W_real,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.re_sum]

@[blueprint "varlamov-zero-pair-split"
  (title := "Varlamov, equation Dsplit")
  (statement := /-- Substitution of $\sigma=1-\mu\eta$ and $h=1-2\mu\eta$
  gives exactly Dsplit, with the actual W transform and the actual smallD.
  The final sum is indexed by m+1 over 0 through M-1, equivalently 1 through M. -/)
  (uses := ["varlamov-small-arguments", "varlamov-exact-transform"])]
theorem zero_pair_split (j : Fin 7) (μ : ℝ) {η : ℝ} (hη : η ≠ 0) :
    zeroPairTerm j μ η = smallD μ +
      Trigonometric.a 1 * (∑ m ∈ Finset.range (Multiplier.length j),
        Multiplier.coefficient j m * realW (argumentOne μ η m)) +
      (∑ n ∈ Finset.range (Multiplier.length j - 1), Multiplier.coefficient j (n + 1) *
        (Trigonometric.a 1 * realW (argumentTwo μ η (n + 1)) - realW (argumentThree μ η (n + 1)))) := by
  have h1 (m : ℕ) : (1 - μ * η - η + (1 - 2 * μ * η) * (m : ℝ)) / η = argumentOne μ η m := by
    unfold argumentOne
    field_simp
    <;> ring
  have h2 (m : ℕ) : (1 - μ * η - 1 + η + (1 - 2 * μ * η) * (m : ℝ)) / η = argumentTwo μ η m := by
    unfold argumentTwo
    field_simp
    <;> ring
  have h3 (m : ℕ) : (1 - μ * η - 1 + (1 - 2 * μ * η) * (m : ℝ)) / η = argumentThree μ η m := by
    unfold argumentThree
    field_simp
    <;> ring
  let f : ℕ → ℝ := fun m => Multiplier.coefficient j m *
    (Trigonometric.a 1 * realW (argumentTwo μ η m) - realW (argumentThree μ η m))
  have hsum : (∑ m ∈ Finset.range (Multiplier.length j), f m) =
      (∑ n ∈ Finset.range (Multiplier.length j - 1), f (n + 1)) + smallD μ := by
    have hl : Multiplier.length j - 1 + 1 = Multiplier.length j := by have := Multiplier.length_pos j; omega
    have he := Finset.sum_range_succ' f (Multiplier.length j - 1)
    rw [hl] at he
    rw [he]
    have hf0 : f 0 = smallD μ := by
      dsimp [f, argumentTwo, argumentThree, smallD]
      rw [Multiplier.coefficient_zero]
      simp only [Nat.cast_zero, mul_zero, zero_div, zero_sub, zero_add, one_mul]
      rw [show - μ + 1 = 1 - μ from by ring]
    rw [hf0]
  unfold zeroPairTerm
  simp_rw [F_real_sum, h1, h2, h3]
  have hcollect :
      Trigonometric.a 1 * ((∑ m ∈ Finset.range (Multiplier.length j), Multiplier.coefficient j m * realW (argumentTwo μ η m)) +
        (∑ m ∈ Finset.range (Multiplier.length j), Multiplier.coefficient j m * realW (argumentOne μ η m))) -
        (∑ m ∈ Finset.range (Multiplier.length j), Multiplier.coefficient j m * realW (argumentThree μ η m)) =
      Trigonometric.a 1 * (∑ m ∈ Finset.range (Multiplier.length j), Multiplier.coefficient j m * realW (argumentOne μ η m)) +
        ∑ m ∈ Finset.range (Multiplier.length j), f m := by
    dsimp only [f]
    simp_rw [mul_sub]
    rw [mul_add, Finset.sum_sub_distrib]
    have hsum2 : (∑ m ∈ Finset.range (Multiplier.length j), Multiplier.coefficient j m *
        (Trigonometric.a 1 * realW (argumentTwo μ η m))) =
        Trigonometric.a 1 * (∑ m ∈ Finset.range (Multiplier.length j),
          Multiplier.coefficient j m * realW (argumentTwo μ η m)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m _
      ring
    rw [hsum2]
    ring

  rw [hcollect, hsum]
  dsimp only [f]
  ring

@[blueprint "varlamov-large-arguments"
  (title := "Varlamov, C13: admissibility of all large transform arguments")
  (statement := /-- All large arguments in Dsplit exceed $1/\eta^+-3>0$
  throughout the parameter domain. This proves the side condition
  analytically, not the still missing positivity of the final margin. -/)
  (uses := ["varlamov-zero-pair-split", "varlamov-band-bounds"])]
theorem large_arguments_bound (j : Fin 7) {μ η : ℝ} (hμ : μ < 1)
    (hη : 0 < η) (hηmax : η < etaMax j) :
    (∀ m : ℕ, 1 / etaMax j - 3 < argumentOne μ η m) ∧
    (∀ m : ℕ, 1 ≤ m → 1 / etaMax j - 3 < argumentTwo μ η m ∧
      1 / etaMax j - 3 < argumentThree μ η m) ∧ 0 < 1 / etaMax j - 3 := by
  have hm := (etaMax_range j).1
  have hm1 := (etaMax_range j).2
  have hInv : 1 / etaMax j < 1 / η := one_div_lt_one_div_of_lt hη hηmax
  have h3 : (3 : ℝ) < 1 / etaMax j := (lt_div_iff₀ hm).mpr (by linarith)
  have hb : 0 < 1 / η - 2 * μ := by linarith
  refine ⟨?_, ?_, by linarith⟩
  · intro m
    have hn : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hp := mul_nonneg hn hb.le
    have he : argumentOne μ η m = (m : ℝ) * (1 / η - 2 * μ) + (1 / η - μ - 1) := by
      unfold argumentOne
      ring
    rw [he]
    nlinarith
  · intro m hmn
    have hn : (1 : ℝ) ≤ m := by exact_mod_cast hmn
    have hp := mul_nonneg (show 0 ≤ (m : ℝ) - 1 by linarith) hb.le
    have he : argumentThree μ η m = ((m : ℝ) - 1) * (1 / η - 2 * μ) + (1 / η - 3 * μ) := by
      unfold argumentThree
      ring
    have hThree : 1 / etaMax j - 3 < argumentThree μ η m := by rw [he]; nlinarith
    refine ⟨?_, hThree⟩
    have hTwo : argumentTwo μ η m = argumentThree μ η m + 1 := by unfold argumentTwo argumentThree; ring
    rw [hTwo]
    linarith

#print axioms large_arguments_bound
#print axioms zero_pair_split
end Varlamov
