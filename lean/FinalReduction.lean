import PrimeNumberTheoremAnd.IEANTN.Varlamov.ZeroSumBounds
import PrimeNumberTheoremAnd.IEANTN.Varlamov.Margin

namespace Varlamov
open Real

/-!
# Conditional end-to-end reduction

This generic reduction displays the two finite certificate premises. They are
not literature inputs. Their concrete proofs are supplied by PhaseCertificates
and ActualMarginCertificate, and FinalRegion assembles the full theorem.
This module keeps the analytic reduction reusable for other certificate data.
-/

@[blueprint "varlamov-final-finite-reduction"
  (title := "C_8a: end-to-end reduction to the two finite certificates")
  (statement := /-- The full closed $R=4.81406$ region follows from the named
  published inputs and the phase and actual-margin certificates. The concrete
  local certificates are proved separately and instantiated in FinalRegion. -/)
  (uses := ["varlamov-minimal-zero", "varlamov-full-zero-sum-bound",
    "varlamov-margin-reduction", "varlamov-zero-free-target"])]
theorem zeroFreeRegion_of_finite_certificates
    (hK : KadiriInput) (hPT : PlattTrudgianInput) (hY : YangInput)
    (hK2 : KadiriExplicitInput) (hK3 : KadiriDigammaInput) (hC : HalfPlaneCauchyInput)
    (hL1 : LehmanMonotoneInput) (hL2 : LehmanSquareTailInput)
    (Jp : Fin 7 → ℕ → ℝ)
    (hPhase : ∀ j : Fin 7, PrimePhaseCertificate j (Jp j))
    (hMargin : MarginCertificate Jp) : ZeroFreeRegion := by
  classical
  by_contra hfail
  obtain ⟨z,hz,hHeight,hDepth,hLog,hmin⟩ := exists_minimal_zero hK hPT hY hfail
  let L := Real.log z.im
  let A := depth z
  have hL0 : 0 < L := lt_trans (by norm_num [Llo]) hLog.1
  have hLne : L ≠ 0 := ne_of_gt hL0
  have hA0 : 0 < A := lt_trans (by norm_num : (0 : ℝ) < 1 / 6) hDepth.1
  obtain ⟨j,hj⟩ := band_cover ⟨hLog.1.le,hLog.2.le⟩
  have hb : InBand j L A := ⟨hj,⟨hDepth.1.le,hDepth.2⟩⟩
  obtain ⟨hhalf,hσlo,hσhi,hmax,hη,hηmax,_,hμlo,hμhi⟩ := band_bounds j hb
  have hh := (band_shift_bounds j hb).1.le
  have hExp : Real.exp L = z.im := Real.exp_log hz.2.2
  have ht : H ≤ Real.exp L := by rw [hExp]; exact hHeight.le
  have hσ1 : sigma L A < 1 := hσhi.trans_lt hmax
  have hσeta : 1 - eta L A ≤ sigma L A := by
    unfold sigma eta
    have hd := div_le_div_of_nonneg_left hA0.le hL0 (show L ≤ logCutoff L from logCutoff_gt.le)
    linarith
  have hAe : eta L A * Real.log (Real.exp L) = A := by
    rw [Real.log_exp]
    unfold eta
    field_simp
  let ρ₀ : NontrivialZeros := ⟨z,⟨⟨by linarith [hz.2.1],zeta_re_lt_one hz.1⟩,Set.mem_univ _,hz.1⟩⟩
  have hβ : (ρ₀ : ℂ).re = 1 - eta L A := by
    change z.re = 1 - A / L
    dsimp [A,L]
    unfold depth
    have hn : Real.log z.im ≠ 0 := hLne
    field_simp
    <;> ring
  have hτ : (ρ₀ : ℂ).im = Real.exp L := hExp.symm
  have hZeros := weighted_zero_bound hK2 hL1 hL2 hPT j hA0 hmin
    (show sigma L A = 1 - A / Real.log (12 * Real.exp L + T0) from rfl)
    ((by linarith : (1 / 2 : ℝ) < sigma L A)) hσ1 hh hσeta hη hηmax.le ht hAe hDepth.2
    ρ₀ hβ hz.2.1 hτ
  have hm := margin_le_zero_of_zero_bound hK2 hK3 hC j (Jp j) (hPhase j) hb ht hZeros
  have hp := hMargin j L A hb
  linarith

#print zeroFreeRegion_of_finite_certificates
#print axioms zeroFreeRegion_of_finite_certificates
end Varlamov
