import PrimeNumberTheoremAnd.IEANTN.Varlamov.GammaPositive

namespace Varlamov
open Real
open scoped BigOperators

/-- Published Stirling remainder: Nemes (2017), section 4, equations
(4.1)--(4.2), with the bound (1.8), N=4 and positive real argument.
https://doi.org/10.1098/rspa.2017.0363
https://pmc.ncbi.nlm.nih.gov/articles/PMC5549576/ .
Also NIST DLMF 5.11.2 and 5.11(ii), https://dlmf.nist.gov/5.11.ii .
This is the specialization with the first three Bernoulli terms. The
first neglected term is B8/(8*x^8) in absolute value, 1/(240*x^8).
The expansion and remainder statement are external inputs, not numerical
certificates or a claim about the present zero-free-region manuscript. -/
def RealDigammaStirlingInput : Prop :=
  ∀ x : ℝ, 0 < x →
    |realDigamma x - (Real.log x - 1 / (2 * x) - 1 / (12 * x ^ 2) +
      1 / (120 * x ^ 4) - 1 / (252 * x ^ 6))| ≤ 1 / (240 * x ^ 8)

noncomputable def digammaApprox (x : ℝ) : ℝ :=
  let y := x + 8
  Real.log y - 1 / (2 * y) - 1 / (12 * y ^ 2) + 1 / (120 * y ^ 4) -
    1 / (252 * y ^ 6) - ∑ k ∈ Finset.range 8, (x + k)⁻¹

lemma realDigamma_add_nat {x : ℝ} (hx : 0 < x) (n : ℕ) :
    realDigamma (x + n) = realDigamma x + ∑ k ∈ Finset.range n, (x + k)⁻¹ := by
  have hp : ∀ m : ℕ, (x : ℂ) ≠ -(m : ℂ) := by
    intro m hm
    have hr := congrArg Complex.re hm
    simp only [Complex.ofReal_re, Complex.neg_re, Complex.natCast_re] at hr
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have he := congrArg Complex.re (Complex.digamma_apply_add_nat hp n)
  simpa only [realDigamma, Complex.ofReal_add, Complex.ofReal_natCast,
    Complex.add_re, Complex.re_sum, ← Complex.ofReal_add, ← Complex.ofReal_natCast,
    ← Complex.ofReal_inv, Complex.ofReal_re] using he

lemma digammaApprox_error (hS : RealDigammaStirlingInput) {x : ℝ} (hx : 1 ≤ x) :
    |realDigamma x - digammaApprox x| ≤ (1e-9 : ℝ) := by
  have hx0 : 0 < x := by linarith
  have hs := hS (x + 8) (by linarith)
  have he := realDigamma_add_nat hx0 8
  norm_num only [Nat.cast_ofNat] at he
  rw [he] at hs
  have hb : 1 / (240 * (x + 8) ^ 8) ≤ (1e-9 : ℝ) := by
    calc
      _ ≤ 1 / (240 * (9 : ℝ) ^ 8) := by gcongr; linarith
      _ ≤ _ := by norm_num
  have heq : realDigamma x - digammaApprox x =
      realDigamma x + (∑ k ∈ Finset.range 8, (x + k)⁻¹) -
        (Real.log (x + 8) - 1 / (2 * (x + 8)) - 1 / (12 * (x + 8) ^ 2) +
          1 / (120 * (x + 8) ^ 4) - 1 / (252 * (x + 8) ^ 6)) := by
    unfold digammaApprox
    ring
  rw [heq]
  exact hs.trans hb

lemma gammaX_ge_one (j : Fin 7) (m : ℕ) : 1 ≤ gammaX j m := by
  have hσ := (sigmaMin_range j).1
  have hσ' := (sigmaMax_range j).1
  have hh := hMin_pos j
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  unfold gammaX
  split_ifs <;> nlinarith

noncomputable def gammaApproxLower (j : Fin 7) : ℝ := -(
  (1 / 2) * (∑ m ∈ Finset.range (Multiplier.length j),
    Multiplier.coefficient j m * digammaApprox (gammaX j m)) -
  (Multiplier.kappa j 1 / 2) * Real.log Real.pi + (Multiplier.kappa j 1 / 2) * gammaLogMoment -
  (aPlus * Multiplier.kappa j 1 / 2) * Real.log (2 * Real.pi) +
  (aPlus * Multiplier.coeffNorm j / 2) * 1e-10 + (Multiplier.coeffNorm j / 2) * 1e-9)

lemma gammaApproxLower_le (hS : RealDigammaStirlingInput) (j : Fin 7) :
    gammaApproxLower j ≤ gammaG j := by
  have hb (m : ℕ) : Multiplier.coefficient j m * realDigamma (gammaX j m) ≤
      Multiplier.coefficient j m * digammaApprox (gammaX j m) +
        |Multiplier.coefficient j m| * 1e-9 := by
    have he := digammaApprox_error hS (gammaX_ge_one j m)
    have h := mul_le_mul_of_nonneg_left he (abs_nonneg (Multiplier.coefficient j m))
    rw [← abs_mul] at h
    have hl := (le_abs_self (Multiplier.coefficient j m *
      (realDigamma (gammaX j m) - digammaApprox (gammaX j m)))).trans h
    nlinarith only [hl]
  have hs := Finset.sum_le_sum (fun m (_ : m ∈ Finset.range (Multiplier.length j)) => hb m)
  rw [Finset.sum_add_distrib, ← Finset.sum_mul] at hs
  change (∑ m ∈ Finset.range (Multiplier.length j),
      Multiplier.coefficient j m * realDigamma (gammaX j m)) ≤
    (∑ m ∈ Finset.range (Multiplier.length j),
      Multiplier.coefficient j m * digammaApprox (gammaX j m)) + Multiplier.coeffNorm j * 1e-9 at hs
  unfold gammaApproxLower gammaG
  linarith only [hs]

#print axioms gammaApproxLower_le
end Varlamov
