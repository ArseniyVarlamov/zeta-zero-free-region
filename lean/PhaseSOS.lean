import PrimeNumberTheoremAnd.IEANTN.Varlamov.IntegerPolynomial
import PrimeNumberTheoremAnd.IEANTN.Varlamov.PrimeLower

namespace Varlamov.PhaseSOS
open Real
open scoped BigOperators

set_option maxRecDepth 8192

def normInteger : ℤ := 1000000000000529836702335
def trigInteger (k : ℕ) : ℤ :=
  ([1000000000000529836702335, 1737030133020229803268728, 1117417276832381755100094, 495623914497151388166062, 120554824393494214603934, 1000228859347402, 999982469344960, 10498128593801130549642, 5685067613122112363670, 999709767505660, 999780584544320, 972747969844526498018, 489492892340708029400] : List ℤ).getD k 0

def weightScale : ℤ := 10000000000000
def factorScale : ℤ := 100000000000000
def targetScale : ℤ := 10000000000
def squareScale : ℤ := 2 * normInteger * weightScale
def totalScale : ℤ := squareScale * factorScale ^ 2
def errorScale : ℤ := squareScale * 1000000000000000000

noncomputable def unit (x : ℝ) : ℂ := Complex.exp ((x : ℂ) * Complex.I)
noncomputable def centered (D : ℕ) (x : ℝ) (p : List ℤ) : ℝ :=
  (((unit x) ^ D)⁻¹ * IntegerPolynomial.eval (unit x) p).re

lemma unit_norm (x : ℝ) : ‖unit x‖ = 1 := by
  simp [unit, Complex.norm_exp]

lemma unit_mul_conj (x : ℝ) : unit x * starRingEnd ℂ (unit x) = 1 := by
  rw [Complex.mul_conj]
  have h := Complex.sq_norm (unit x)
  rw [unit_norm] at h
  norm_num at h
  exact_mod_cast h.symm

lemma centered_add (D : ℕ) (x : ℝ) (p q : List ℤ) :
    centered D x (IntegerPolynomial.add p q) = centered D x p + centered D x q := by
  simp [centered, IntegerPolynomial.eval_add, mul_add]

lemma centered_scale (D : ℕ) (x : ℝ) (a : ℤ) (p : List ℤ) :
    centered D x (IntegerPolynomial.scale a p) = (a : ℝ) * centered D x p := by
  unfold centered
  rw [IntegerPolynomial.eval_scale, ← mul_assoc, mul_comm _ (a : ℂ), mul_assoc]
  simp

lemma centered_sumRange (D : ℕ) (x : ℝ) (n : ℕ) (f : ℕ → List ℤ) :
    centered D x (IntegerPolynomial.sumRange n f) = ∑ i ∈ Finset.range n, centered D x (f i) := by
  simp [centered, IntegerPolynomial.eval_sumRange, Finset.mul_sum, Complex.re_sum]

lemma unit_pow (x : ℝ) (n : ℕ) :
    unit x ^ n = Complex.exp ((((n : ℝ) * x : ℝ) : ℂ) * Complex.I) := by
  rw [unit, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

lemma centered_monomial (D n : ℕ) (x : ℝ) (a : ℤ) :
    centered D x (IntegerPolynomial.monomial a n) = (a : ℝ) * Real.cos (((n : ℝ) - D) * x) := by
  unfold centered
  rw [IntegerPolynomial.eval_monomial]
  have he : (unit x ^ D)⁻¹ * (unit x ^ n) =
      Complex.exp (((((n : ℝ) - D) * x : ℝ) : ℂ) * Complex.I) := by
    rw [unit_pow, unit_pow, ← div_eq_inv_mul, ← Complex.exp_sub]
    congr 1
    push_cast
    ring
  rw [show (unit x ^ D)⁻¹ * ((a : ℂ) * unit x ^ n) =
      (a : ℂ) * ((unit x ^ D)⁻¹ * unit x ^ n) from by ring, he]
  simp [Complex.exp_re]

lemma centered_abs_le (D : ℕ) (x : ℝ) (p : List ℤ) :
    |centered D x p| ≤ (IntegerPolynomial.absSum p : ℝ) := by
  apply (Complex.abs_re_le_norm _).trans
  rw [norm_mul, norm_inv, norm_pow, unit_norm, one_pow, inv_one, one_mul]
  exact IntegerPolynomial.eval_norm_le (unit_norm x).le p

lemma trigInteger_eq {k : ℕ} (hk : k < 13) :
    (trigInteger k : ℝ) = (normInteger : ℝ) * Trigonometric.a k := by
  interval_cases k <;> norm_num [trigInteger, normInteger, Trigonometric.a]

def term (D r : ℕ) (w : ℤ) : List ℤ :=
  IntegerPolynomial.sumRange 13 (fun k => IntegerPolynomial.add
    (IntegerPolynomial.monomial (w * trigInteger k) (D + r * k))
    (IntegerPolynomial.monomial (w * trigInteger k) (D - r * k)))

def phasePoly (D : ℕ) (weights : List ℤ) : List ℤ :=
  IntegerPolynomial.sumRange weights.length (fun r => term D (r + 1) (weights.getD r 0))

noncomputable def roundedPhase (weights : List ℤ) (x : ℝ) : ℝ :=
  ∑ r ∈ Finset.range weights.length,
    ((weights.getD r 0 : ℤ) : ℝ) / weightScale * Trigonometric.P (((r + 1 : ℕ) : ℝ) * x)

lemma centered_term (D r : ℕ) (w : ℤ) (hr : 12 * r ≤ D) (x : ℝ) :
    centered D x (term D r w) =
      2 * (w : ℝ) * normInteger * Trigonometric.P ((r : ℝ) * x) := by
  rw [term, centered_sumRange]
  unfold Trigonometric.P
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k < 13 := Finset.mem_range.mp hk
  have hkr : r * k ≤ D := by
    calc
      r * k ≤ r * 12 := Nat.mul_le_mul_left r (by omega)
      _ = 12 * r := Nat.mul_comm _ _
      _ ≤ D := hr
  rw [centered_add, centered_monomial, centered_monomial, Nat.cast_add, Nat.cast_sub hkr]
  rw [Int.cast_mul, trigInteger_eq hk']
  push_cast
  have he1 : (((D : ℝ) + (r : ℝ) * k) - D) * x = (k : ℝ) * ((r : ℝ) * x) := by ring
  have he2 : (((D : ℝ) - (r : ℝ) * k) - D) * x = -((k : ℝ) * ((r : ℝ) * x)) := by ring
  rw [he1, he2, Real.cos_neg]
  ring

lemma centered_phasePoly (D : ℕ) (weights : List ℤ) (hD : 12 * weights.length ≤ D) (x : ℝ) :
    centered D x (phasePoly D weights) =
      (squareScale : ℝ) * roundedPhase weights x := by
  rw [phasePoly, centered_sumRange]
  unfold roundedPhase
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  rw [centered_term D (r + 1) (weights.getD r 0) (by have := Finset.mem_range.mp hr; omega)]
  norm_num [squareScale, weightScale]
  ring

/-- The integer residual of the proposed Fejer-Riesz identity. -/
def residual (D : ℕ) (weights factor : List ℤ) (target : ℤ) : List ℤ :=
  IntegerPolynomial.add (IntegerPolynomial.scale (factorScale ^ 2) (phasePoly D weights))
    (IntegerPolynomial.add (IntegerPolynomial.scale (-squareScale) (IntegerPolynomial.mul factor factor.reverse))
      (IntegerPolynomial.monomial (-(target * errorScale)) D))

/-- This executable check uses integer arithmetic only. -/
def check (D : ℕ) (weights factor : List ℤ) (target : ℤ) : Bool :=
  decide (12 * weights.length ≤ D ∧ factor.length = D + 1 ∧
    IntegerPolynomial.absSum (residual D weights factor target) ≤ errorScale)

/-- A checked rational lower bound for the true trigonometric polynomial
with the given rational weights. Actual-weight comparisons are separate. -/
theorem checked_lower_bound (D : ℕ) (weights factor : List ℤ) (target : ℤ)
    (hc : check D weights factor target = true) (x : ℝ) :
    (((target - 1 : ℤ) : ℝ) / targetScale) ≤ roundedPhase weights x := by
  have hc' := of_decide_eq_true hc
  rcases hc' with ⟨hD,hlen,hres⟩
  have hn : factor ≠ [] := by intro he; simp [he] at hlen
  have hsq := IntegerPolynomial.centered_square_nonneg (unit_mul_conj x) factor hn
  have hlen' : factor.length - 1 = D := by omega
  change 0 ≤ centered (factor.length - 1) x (IntegerPolynomial.mul factor factor.reverse) at hsq
  rw [hlen'] at hsq
  have hres' := centered_abs_le D x (residual D weights factor target)
  have hr : -((errorScale : ℤ) : ℝ) ≤ centered D x (residual D weights factor target) := by
    exact (neg_le_of_abs_le (hres'.trans (by exact_mod_cast hres)))
  rw [residual, centered_add, centered_scale, centered_add, centered_scale,
    centered_monomial, centered_phasePoly D weights hD] at hr
  norm_num only [Int.cast_neg, Int.cast_mul, Nat.cast_id, sub_self, zero_mul,
    Real.cos_zero, mul_one] at hr
  norm_num [targetScale, factorScale, errorScale, squareScale, weightScale, normInteger] at *
  push_cast
  nlinarith

#print axioms checked_lower_bound
end Varlamov.PhaseSOS
