import PrimeNumberTheoremAnd.IEANTN.Varlamov.Definitions
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! # The minimum-principle step in paired positivity

The real part minimum principle is derived from Mathlib's maximum modulus
principle by applying it to exp(-G). No new analytic axiom is introduced.
-/

namespace Varlamov
open Real

lemma re_nonneg_of_frontier {G : ℂ → ℂ} {S : Set ℂ}
    (hS : Bornology.IsBounded S) (hG : DiffContOnCl ℂ G S)
    (hbd : ∀ z ∈ frontier S, 0 ≤ (G z).re) {z : ℂ} (hz : z ∈ closure S) :
    0 ≤ (G z).re := by
  have he : DiffContOnCl ℂ (fun z => Complex.exp (-G z)) S := by
    exact ⟨hG.differentiableOn.neg.cexp, hG.continuousOn.neg.cexp⟩
  have hbe : ∀ w ∈ frontier S, ‖Complex.exp (-G w)‖ ≤ 1 := by
    intro w hw
    rw [Complex.norm_exp, Complex.neg_re, Real.exp_le_one_iff]
    linarith [hbd w hw]
  have h := Complex.norm_le_of_forall_mem_frontier_norm_le hS he hbe hz
  rw [Complex.norm_exp, Complex.neg_re, Real.exp_le_one_iff] at h
  linarith

#print axioms re_nonneg_of_frontier

end Varlamov
