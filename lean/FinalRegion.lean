import PrimeNumberTheoremAnd.IEANTN.Varlamov.HalfPlaneCauchyProof
import PrimeNumberTheoremAnd.IEANTN.Varlamov.PhaseCertificates
import PrimeNumberTheoremAnd.IEANTN.Varlamov.ActualMarginCertificate

namespace Varlamov
open Real

/-- The full C_8a theorem, with closed real-part boundary and absolute
height at least two. All local analytic and numerical obligations are proved;
the eight remaining parameters are explicitly named published results. -/
@[blueprint "varlamov-zero-free-region"
  (title := "Varlamov, Theorem 1.1: the full R=4.81406 zero-free region")
  (statement := /-- Under the eight explicitly named published inputs,
  $\zeta(\sigma+it)\ne0$ for $|t|\ge2$ and
  $\sigma\ge1-1/(4.81406\log|t|)$, including the boundary.
  Every local analytic and numerical lemma is proved in Lean. -/)
  (uses := ["varlamov-final-finite-reduction", "varlamov-certified-phase-minima",
    "varlamov-actual-margin-certificate", "varlamov-half-plane-cauchy"])]
theorem c8a_zero_free_region
    (hK : KadiriInput) (hPT : PlattTrudgianInput) (hY : YangInput)
    (hK2 : KadiriExplicitInput) (hK3 : KadiriDigammaInput) 
    (hL1 : LehmanMonotoneInput) (hL2 : LehmanSquareTailInput)
    (hS : RealDigammaStirlingInput) : ZeroFreeRegion :=
  zeroFreeRegion_of_finite_certificates hK hPT hY hK2 hK3 halfPlaneCauchyInput_proved hL1 hL2 phaseLower
    phaseLower_certificate (actual_margin_certificate hS)

/-- The same theorem in the existing PNT+ convention. -/
theorem c8a_classical_zero_free
    (hK : KadiriInput) (hPT : PlattTrudgianInput) (hY : YangInput)
    (hK2 : KadiriExplicitInput) (hK3 : KadiriDigammaInput) 
    (hL1 : LehmanMonotoneInput) (hL2 : LehmanSquareTailInput)
    (hS : RealDigammaStirlingInput) : riemannZeta.classicalZeroFree R :=
  (c8a_zero_free_region hK hPT hY hK2 hK3 hL1 hL2 hS).classicalZeroFree

/-- Literal decimal formulation of the author's target. -/
theorem c8a_nonvanishing
    (hK : KadiriInput) (hPT : PlattTrudgianInput) (hY : YangInput)
    (hK2 : KadiriExplicitInput) (hK3 : KadiriDigammaInput) 
    (hL1 : LehmanMonotoneInput) (hL2 : LehmanSquareTailInput)
    (hS : RealDigammaStirlingInput) {σ t : ℝ}
    (ht : 2 ≤ |t|) (hσ : 1 - 1 / ((4.81406 : ℝ) * Real.log |t|) ≤ σ) :
    riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
  apply c8a_zero_free_region hK hPT hY hK2 hK3 hL1 hL2 hS σ t ht
  simpa only [R_decimal] using hσ

#print c8a_zero_free_region
#print c8a_nonvanishing
#print axioms c8a_zero_free_region
#print axioms c8a_classical_zero_free
#print axioms c8a_nonvanishing
end Varlamov
