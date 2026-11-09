import PrimeNumberTheoremAnd.IEANTN.Varlamov.ShiftedZeroTail
import PrimeNumberTheoremAnd.IEANTN.Varlamov.DistinguishedPair

namespace Varlamov
open Real
open scoped BigOperators

lemma S_nonneg (j : Fin 7) : 0 ≤ S j := by
  unfold S
  have hc := Kernel.Cminus_pos
  have hn := Multiplier.coeffNorm_nonneg j
  have hT : (0 : ℝ) < T0 := by norm_num [T0]
  positivity

lemma zeroTailNonreal_baseline (j : Fin 7) : S j * Astar / (8 * T0) ≤ zeroTailNonreal j := by
  have hT : (0 : ℝ) < T0 := by norm_num [T0]
  have hH : (0 : ℝ) < H := by norm_num [H]
  have hLog : 0 < Real.log H := by linarith [log_height_bounds.1]
  have hp := Real.pi_pos
  obtain ⟨h10,h13⟩ := lambdaOne_bounds
  obtain ⟨h20,h23⟩ := lambdaTwo_bounds
  obtain ⟨h30,h3u⟩ := lambdaThree_bounds
  have hbase : 1 / (8 * T0) ≤ 1 / (2 * Real.pi * T0) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    nlinarith [Real.pi_lt_four]
  have h1 : 1 / (2 * Real.pi * T0) ≤ (1 + lambdaOne / Real.log H) / (2 * Real.pi * T0) :=
    div_le_div_of_nonneg_right (by
      have hq : 0 ≤ lambdaOne / Real.log H := by positivity
      linarith) (by positivity)
  have h2 : 0 ≤ lambdaThree / (2 * Real.pi * Real.log H) := by positivity
  have h3 : 0 ≤ 8 * (1 + lambdaTwo / Real.log H) / T0 ^ 2 := by positivity
  have h4 : 0 ≤ 4 / (H * T0 * Real.log H) := by positivity
  unfold zeroTailNonreal
  have hcore : 1 / (8 * T0) ≤ (1 + lambdaOne / Real.log H) / (2 * Real.pi * T0) +
      lambdaThree / (2 * Real.pi * Real.log H) + 8 * (1 + lambdaTwo / Real.log H) / T0 ^ 2 + 4 / (H * T0 * Real.log H) := by
    linarith only [hbase,h1,h2,h3,h4]
  have h := mul_le_mul_of_nonneg_left hcore (mul_nonneg (S_nonneg j) Astar_pos.le)
  convert h using 1 <;> ring

noncomputable def highPairedTerm (j : Fin 7) (σ η τ T : ℝ) (ρ : NontrivialZeros) : ℝ :=
  if T < |(ρ : ℂ).im| then Pi j (2 * σ - 1) η (((σ : ℂ) + (τ : ℂ) * Complex.I) - ρ) * (riemannZeta.order ρ : ℝ) else 0

lemma highPairedTerm_summable (hK2 : KadiriExplicitInput) (j : Fin 7) {σ η τ T : ℝ}
    (hσ : (1 / 2 : ℝ) < σ) (hh : 0 ≤ 2 * σ - 1) (hη : 0 < η) : Summable (highPairedTerm j σ η τ T) := by
  classical
  have hs := paired_zero_sum_summable hK2 j (s := (σ : ℂ) + (τ : ℂ) * Complex.I)
    hh hη (by simpa using hσ) (by simp)
  apply (hs.indicator {ρ : NontrivialZeros | T < |(ρ : ℂ).im|}).congr
  intro ρ
  simp only [highPairedTerm, Set.indicator_apply, Set.mem_ofPred_eq]

@[blueprint "varlamov-nonreal-zero-tail"
  (title := "Varlamov, Lemma 7.1: nonreal high-zero loss")
  (statement := /-- Half of the paired high-zero sum is at least $-Z_+$
  at every nonzero trigonometric frequency. Lehman's published finite-window
  and square-tail bounds are named inputs. All calculus, summability,
  conjugation and cutoff comparisons are proved here. -/)
  (uses := ["varlamov-off-strip", "varlamov-tail-constants", "varlamov-zero-reflection-order"])]
theorem nonreal_high_zero_bound (hK2 : KadiriExplicitInput) (hL1 : LehmanMonotoneInput)
    (hL2 : LehmanSquareTailInput) (j : Fin 7) {σ η t A : ℝ} {k : ℕ}
    (hσ : (1 / 2 : ℝ) < σ) (hσ1 : σ < 1) (hh : hMin j ≤ 2 * σ - 1) (hσeta : 1 - η ≤ σ)
    (hη : 0 < η) (hηmax : η ≤ etaMax j) (ht : H ≤ t) (hk1 : 1 ≤ k) (hk12 : k ≤ 12)
    (hA : η * Real.log t = A) (hAmax : A ≤ Astar) :
    - zeroTailNonreal j ≤ (1 / 2 : ℝ) * (∑' ρ : NontrivialZeros,
      highPairedTerm j σ η ((k : ℝ) * t) (12 * t + T0) ρ) := by
  let τ := (k : ℝ) * t
  let T := 12 * t + T0
  let L := Real.log t
  have hH : (0 : ℝ) < H := by norm_num [H]
  have hT0 : (0 : ℝ) < T0 := by norm_num [T0]
  have ht0 : 0 < t := hH.trans_le ht
  have hkR1 : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hkR12 : (k : ℝ) ≤ 12 := by exact_mod_cast hk12
  have hτH : H ≤ τ := by dsimp [τ]; nlinarith
  have hτ : 0 < τ := hH.trans_le hτH
  have hgap : T0 ≤ T - τ := by dsimp [T,τ]; nlinarith
  have hτT : τ < T := by linarith
  have hTT0 : T0 ≤ T := by linarith
  have hAd := T0_Lehman_admissible.trans hTT0
  have hL : 28 ≤ L := (log_height_bounds.1.le).trans (Real.log_le_log hH ht)
  have hLog : Real.log T ≤ L + 3 := log_cutoff_le_log_height_plus_three ht
  have hPhi := uniform_positivePhiTail_bound hL1 hL2 hτH hgap hLog hL
  have hShift := shiftedSquareTail_eq_phi hL2 hτ hτT hAd
  have hG : (∑' ρ : NontrivialZeros, shiftedSquareTail τ T ρ) ≤ L / (4 * T0) := by rw [hShift.2]; exact hPhi.2
  have hh0 : 0 ≤ 2 * σ - 1 := (hMin_pos j).le.trans hh
  have hhI : 2 * σ - 1 ∈ Set.Ico (hMin j) 1 := ⟨hh, by linarith⟩
  have hsHigh := highPairedTerm_summable hK2 j (τ := τ) (T := T) hσ hh0 hη
  have hpoint (ρ : NontrivialZeros) : (-S j * η) * shiftedSquareTail τ T ρ ≤ highPairedTerm j σ η τ T ρ := by
    have ho : 0 ≤ (riemannZeta.order ρ : ℝ) := by exact_mod_cast zeta_order_nonneg (nontrivial_ne_one ρ)
    by_cases hc : T < |(ρ : ℂ).im|
    · have hx : ((((σ : ℂ) + (τ : ℂ) * Complex.I) - (ρ : ℂ))).re ∈ Set.Icc (-η) ((2 * σ - 1) + η) := by
        simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_I_re, Complex.ofReal_im, add_zero]
        constructor <;> linarith [ρ.property.1.1, ρ.property.1.2]
      have htri : |(ρ : ℂ).im| ≤ |τ - (ρ : ℂ).im| + τ := by
        have h := abs_add_le ((ρ : ℂ).im - τ) τ
        rw [sub_add_cancel, abs_sub_comm, abs_of_pos hτ] at h
        exact h
      have hy : T0 ≤ |((((σ : ℂ) + (τ : ℂ) * Complex.I) - (ρ : ℂ))).im| := by
        simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_I_im, Complex.ofReal_re, zero_add]
        linarith
      have hb := mul_le_mul_of_nonneg_right (off_strip_bound j hhI hη hηmax hx hy) ho
      simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_I_im, Complex.ofReal_re, zero_add] at hb
      simp only [shiftedSquareTail, highPairedTerm, ite_eq_left hc]
      convert hb using 1 <;> ring
    · simp [shiftedSquareTail, highPairedTerm, hc]
  have hSum := (hShift.1.mul_left (-S j * η)).tsum_le_tsum hpoint hsHigh
  rw [tsum_mul_left] at hSum
  have hNeg : -S j * η ≤ 0 := by have := S_nonneg j; nlinarith
  have hTail := (mul_le_mul_of_nonpos_left hG hNeg).trans hSum
  have hHalf := mul_le_mul_of_nonneg_left hTail (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hAlower : -(S j * Astar / (8 * T0)) ≤ -(S j * A / (8 * T0)) := by
    apply neg_le_neg
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hAmax (S_nonneg j)) (by positivity)
  calc
    - zeroTailNonreal j ≤ -(S j * Astar / (8 * T0)) := neg_le_neg (zeroTailNonreal_baseline j)
    _ ≤ -(S j * A / (8 * T0)) := hAlower
    _ = (1 / 2 : ℝ) * ((-S j * η) * (L / (4 * T0))) := by rw [←hA]; dsimp [L]; ring
    _ ≤ _ := hHalf

#print axioms nonreal_high_zero_bound
end Varlamov
