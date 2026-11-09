import PrimeNumberTheoremAnd.IEANTN.Varlamov.Numbers
import Mathlib.Tactic.FinCases

namespace Varlamov
open Real

/-! All decimals in this file are exact rational numbers from the article. -/
noncomputable def bandLo (j : Fin 7) : ℝ :=
  match j.val with
  | 0 => (17956 / 625)
  | 1 => 45
  | 2 => 60
  | 3 => 70
  | 4 => 77
  | 5 => 80
  | _ => 82

noncomputable def bandHi (j : Fin 7) : ℝ :=
  match j.val with
  | 0 => 45
  | 1 => 60
  | 2 => 70
  | 3 => 77
  | 4 => 80
  | 5 => 82
  | _ => (8232067 / 100000)

noncomputable def sigmaMin (j : Fin 7) : ℝ :=
  match j.val with
  | 0 => (99334529 / 100000000)
  | 1 => (6222659 / 6250000)
  | 2 => (49833779 / 50000000)
  | 3 => (49856711 / 50000000)
  | 4 => (4986933 / 5000000)
  | 5 => (19949633 / 20000000)
  | _ => (49877063 / 50000000)

noncomputable def etaMax (j : Fin 7) : ℝ :=
  match j.val with
  | 0 => (180759 / 25000000)
  | 1 => (115403 / 25000000)
  | 2 => (34621 / 10000000)
  | 3 => (296751 / 100000000)
  | 4 => (134887 / 50000000)
  | 5 => (129829 / 50000000)
  | _ => (10133 / 4000000)

noncomputable def pairedEps (j : Fin 7) : ℝ :=
  match j.val with
  | 0 => (12169 / 25000000)
  | 1 => (3907 / 20000000)
  | 2 => (10913 / 100000000)
  | 3 => (3997 / 50000000)
  | 4 => (1649 / 25000000)
  | 5 => (6107 / 100000000)
  | _ => (581 / 10000000)

noncomputable def logCutoff (L : ℝ) : ℝ := log (12 * exp L + 10000000000)
noncomputable def eta (L A : ℝ) : ℝ := A / L
noncomputable def sigma (L A : ℝ) : ℝ := 1 - A / logCutoff L
noncomputable def mu (L : ℝ) : ℝ := L / logCutoff L
noncomputable def sigmaMax (j : Fin 7) : ℝ := 1 - (1 / 6) / logCutoff (bandHi j)

def InBand (j : Fin 7) (L A : ℝ) : Prop :=
  L ∈ Set.Icc (bandLo j) (bandHi j) ∧ A ∈ Set.Icc (1 / 6 : ℝ) Astar

lemma band_cover {L : ℝ} (hL : L ∈ Set.Icc Llo Lhi) :
    ∃ j : Fin 7, L ∈ Set.Icc (bandLo j) (bandHi j) := by
  by_cases h1 : L ≤ 45
  · exact ⟨0, by norm_num [bandLo, bandHi, Llo] at * ; tauto⟩
  by_cases h2 : L ≤ 60
  · exact ⟨1, by norm_num [bandLo, bandHi]; constructor <;> linarith⟩
  by_cases h3 : L ≤ 70
  · exact ⟨2, by norm_num [bandLo, bandHi]; constructor <;> linarith⟩
  by_cases h4 : L ≤ 77
  · exact ⟨3, by norm_num [bandLo, bandHi]; constructor <;> linarith⟩
  by_cases h5 : L ≤ 80
  · exact ⟨4, by norm_num [bandLo, bandHi]; constructor <;> linarith⟩
  by_cases h6 : L ≤ 82
  · exact ⟨5, by norm_num [bandLo, bandHi]; constructor <;> linarith⟩
  · exact ⟨6, by norm_num [bandLo, bandHi, Lhi] at * ; constructor <;> linarith [hL.2]⟩

lemma bandLo_pos (j : Fin 7) : 0 < bandLo j := by fin_cases j <;> norm_num [bandLo]
lemma bandLo_ge (j : Fin 7) : Llo ≤ bandLo j := by fin_cases j <;> norm_num [bandLo, Llo]
lemma band_endpoints (j : Fin 7) : bandLo j < bandHi j := by
  fin_cases j <;> norm_num [bandLo, bandHi]
lemma sigmaMin_range (j : Fin 7) : 0.99 < sigmaMin j ∧ sigmaMin j < 1 := by
  fin_cases j <;> norm_num [sigmaMin]
lemma etaMax_range (j : Fin 7) : 0 < etaMax j ∧ etaMax j < 0.01 := by
  fin_cases j <;> norm_num [etaMax]
lemma pairedEps_range (j : Fin 7) : 0 < pairedEps j ∧ pairedEps j < 1 := by
  fin_cases j <;> norm_num [pairedEps]

/-- Check C5: strict lower bound for sigma. -/
lemma sigmaMin_check (j : Fin 7) : sigmaMin j < 1 - Astar / logCutoff (bandLo j) := by
  fin_cases j <;> unfold sigmaMin Astar logCutoff bandLo <;>
    norm_num only [Fin.reduceFinMk] <;> interval_decide (trust := kernel) <;> ring

/-- Check C5: strict upper bound for eta. -/
lemma etaMax_check (j : Fin 7) : Astar / bandLo j < etaMax j := by
  fin_cases j <;> norm_num [Astar, bandLo, etaMax]

lemma logCutoff_gt {L : ℝ} : L < logCutoff L := by
  have h : exp L < 12 * exp L + 10000000000 := by nlinarith [exp_pos L]
  simpa [logCutoff] using log_lt_log (exp_pos L) h

lemma logCutoff_mono : Monotone logCutoff := by
  intro L M h
  apply log_le_log (by positivity : 0 < 12 * exp L + 10000000000)
  nlinarith [exp_le_exp.mpr h]

lemma mu_range {L : ℝ} (hL : Llo ≤ L) : (9 / 10 : ℝ) < mu L ∧ mu L < 1 := by
  have hL0 : 0 < L := lt_of_lt_of_le (by norm_num [Llo]) hL
  have hq : 0 < logCutoff L := hL0.trans logCutoff_gt
  have hc : log (10000000000 : ℝ) < Llo := by
    unfold Llo
    interval_decide (trust := kernel)
  have hten : (10000000000 : ℝ) < exp L :=
    (log_lt_iff_lt_exp (by norm_num)).mp (hc.trans_le hL)
  have h13 : log (13 : ℝ) < Llo / 9 := by
    unfold Llo
    interval_decide (trust := kernel)
  have hu : logCutoff L < L + log 13 := by
    have h := log_lt_log (by positivity : 0 < 12 * exp L + 10000000000)
      (show 12 * exp L + 10000000000 < 13 * exp L by linarith)
    simpa [logCutoff, log_mul (by norm_num : (13 : ℝ) ≠ 0) (ne_of_gt (exp_pos L)),
      add_comm] using h
  constructor
  · dsimp [mu]
    apply (lt_div_iff₀ hq).mpr
    have hm : log 13 < L / 9 := h13.trans_le (div_le_div_of_nonneg_right hL (by norm_num))
    nlinarith
  · exact (div_lt_one hq).mpr logCutoff_gt

@[blueprint "varlamov-band-bounds"
  (title := "Varlamov, Lemma 3.2: band bounds")
  (statement := /-- On each closed height-depth rectangle, the rational band constants
  give the claimed strict lower and upper parameter bounds. -/)
  (uses := ["varlamov-minimal-zero"])]
theorem band_bounds (j : Fin 7) {L A : ℝ} (hb : InBand j L A) :
    1 / 2 < sigmaMin j ∧ sigmaMin j < sigma L A ∧ sigma L A ≤ sigmaMax j ∧
    sigmaMax j < 1 ∧ 0 < eta L A ∧ eta L A < etaMax j ∧ etaMax j < 1 ∧
    (9 / 10 : ℝ) < mu L ∧ mu L < 1 := by
  have hL : 0 < L := (bandLo_pos j).trans_le hb.1.1
  have hqlo : 0 < logCutoff (bandLo j) := (bandLo_pos j).trans logCutoff_gt
  have hq : 0 < logCutoff L := hL.trans logCutoff_gt
  have hqhi : 0 < logCutoff (bandHi j) :=
    ((bandLo_pos j).trans (band_endpoints j)).trans logCutoff_gt
  have hA : 0 < A := lt_of_lt_of_le (by norm_num) hb.2.1
  have hlower : A / logCutoff L ≤ Astar / logCutoff (bandLo j) :=
    (div_le_div_of_nonneg_right hb.2.2 hq.le).trans
      (div_le_div_of_nonneg_left Astar_pos.le hqlo (logCutoff_mono hb.1.1))
  have hupper : (1 / 6 : ℝ) / logCutoff (bandHi j) ≤ A / logCutoff L :=
    (div_le_div_of_nonneg_left (by norm_num) hq (logCutoff_mono hb.1.2)).trans
      (div_le_div_of_nonneg_right hb.2.1 hq.le)
  have het : eta L A < etaMax j :=
    ((div_le_div_of_nonneg_right hb.2.2 hL.le).trans
      (div_le_div_of_nonneg_left Astar_pos.le (bandLo_pos j) hb.1.1)).trans_lt
        (etaMax_check j)
  have hmu := mu_range ((bandLo_ge j).trans hb.1.1)
  refine ⟨by linarith [(sigmaMin_range j).1], ?_, ?_, ?_, div_pos hA hL, het,
    by linarith [(etaMax_range j).2], hmu.1, hmu.2⟩
  · dsimp [sigma]
    linarith [sigmaMin_check j]
  · dsimp [sigma, sigmaMax]
    linarith
  · dsimp [sigmaMax]
    have : 0 < (1 / 6 : ℝ) / logCutoff (bandHi j) := div_pos (by norm_num) hqhi
    linarith

#print axioms band_bounds

end Varlamov
