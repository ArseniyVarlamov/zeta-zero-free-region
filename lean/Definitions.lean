import PrimeNumberTheoremAnd.IEANTN.ZetaDefinitions
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Varlamov's C_8a parameters and external inputs

External inputs are ordinary proposition parameters, never new axioms or imported
unfinished upstream theorems. The author's new analytic lemmas are not external inputs.
The manuscript is `papers/c8a/main.tex`; the numerical companion snapshot is
`zeta-zero-free-region` commit 7235b86064b6.
-/

namespace Varlamov

open Real
open scoped ComplexConjugate

noncomputable def R : ℝ := 240703 / 50000
noncomputable def Astar : ℝ := 50000 / 240703
noncomputable def H : ℝ := 3000000000000
noncomputable def Llo : ℝ := 28.7296
noncomputable def Lhi : ℝ := 82.32067

@[blueprint "varlamov-zero-free-target"
  (title := "Varlamov, Theorem 1.1: target statement")
  (statement := /-- The proposed zero-free region has parameter $R=240703/50000$,
  absolute height at least $2$, and a closed real-part boundary. -/)]
def ZeroFreeRegion : Prop :=
  ∀ σ t : ℝ, 2 ≤ |t| → 1 - 1 / (R * log |t|) ≤ σ →
    riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0

/-- Kadiri, Acta Arith. 117 (2005), Theorem 1.1.
https://doi.org/10.4064/aa117-4-1 . Positive-height restriction of input (K1). -/
def KadiriInput : Prop :=
  ∀ σ t : ℝ, 2 ≤ t → 1 - 1 / ((5.69693 : ℝ) * log t) ≤ σ →
    riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0

/-- Platt--Trudgian, BLMS 53 (2021), Theorem 1.
https://doi.org/10.1112/blms.12460 . Uses the existing PNT+ predicate. -/
def PlattTrudgianInput : Prop := riemannZeta.RH_up_to H

/-- Yang, JMAA 534 (2024), Corollary 1.2, arXiv:2301.03165v2.
https://doi.org/10.1016/j.jmaa.2024.128124 . The strict boundary is essential. -/
def YangInput : Prop :=
  ∀ σ t : ℝ, 3 ≤ t → 1 - log (log t) / (21.233 * log t) < σ →
    riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0

noncomputable def depth (z : ℂ) : ℝ := (1 - z.re) * log z.im

def Admissible (z : ℂ) : Prop :=
  riemannZeta z = 0 ∧ 1 / 2 < z.re ∧ 0 < z.im

def Candidate (z : ℂ) : Prop := Admissible z ∧ depth z ≤ Astar

lemma R_pos : 0 < R := by norm_num [R]
lemma Astar_pos : 0 < Astar := by norm_num [Astar]
lemma Astar_eq_one_div_R : Astar = 1 / R := by norm_num [Astar, R]
lemma R_lt_BTY : R < (4.896 : ℝ) := by norm_num [R]
lemma R_lt_BTY_thesis : R < (4.8594 : ℝ) := by norm_num [R]
lemma R_decimal : R = (4.81406 : ℝ) := by norm_num [R]

lemma region_iff_depth {σ t r : ℝ} (ht : 0 < log t) (_hr : r ≠ 0) :
    1 - 1 / (r * log t) ≤ σ ↔ (1 - σ) * log t ≤ 1 / r := by
  have hid : 1 / (r * log t) = (1 / r) / log t := by ring
  rw [hid]
  constructor
  · intro h
    have : 1 - σ ≤ (1 / r) / log t := by linarith
    exact (le_div_iff₀ ht).mp this
  · intro h
    have := (le_div_iff₀ ht).mpr h
    linarith

lemma zeta_re_lt_one {z : ℂ} (hz : riemannZeta z = 0) : z.re < 1 := by
  by_contra h
  exact riemannZeta_ne_zero_of_one_le_re (le_of_not_gt h) hz

lemma zeta_eq_zero_conj {z : ℂ} (hz : riemannZeta z = 0) :
    riemannZeta (conj z) = 0 := by
  rw [riemannZeta_conj, hz, map_zero]

/-- The positive-height convention of the existing PNT+ predicate. -/
theorem ZeroFreeRegion.classicalZeroFree (h : ZeroFreeRegion) :
    riemannZeta.classicalZeroFree R := by
  intro σ t ht hσ
  have ht0 : 0 ≤ t := by linarith
  simpa [abs_of_nonneg ht0] using h σ t (by simpa [abs_of_nonneg ht0] using
    (show (2 : ℝ) ≤ t by linarith)) (by simpa [abs_of_nonneg ht0] using hσ)

end Varlamov
