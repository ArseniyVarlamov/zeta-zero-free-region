import PrimeNumberTheoremAnd.IEANTN.Varlamov.FinalReduction
import Mathlib.Algebra.Field.Periodic

namespace Varlamov
open Real

lemma P_periodic : Function.Periodic Trigonometric.P (2 * Real.pi) := by
  intro x
  unfold Trigonometric.P
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  rw [show (k : ℝ) * (x + 2 * Real.pi) = (k : ℝ) * x + (k : ℝ) * (2 * Real.pi) from by ring,
    Real.cos_add_nat_mul_two_pi]

lemma primePhase_periodic (j : Fin 7) (p : ℕ) : Function.Periodic (primePhase j p) (2 * Real.pi) := by
  intro x
  unfold primePhase
  apply Finset.sum_congr rfl
  intro n _
  congr 1
  rw [show ((n + 1 : ℕ) : ℝ) * (x + 2 * Real.pi) = ((n + 1 : ℕ) : ℝ) * x + ((n + 1 : ℕ) : ℝ) * (2 * Real.pi) from by ring]
  exact (P_periodic.nat_mul (n + 1)) _

lemma P_continuous : Continuous Trigonometric.P := by unfold Trigonometric.P; fun_prop
lemma primePhase_continuous (j : Fin 7) (p : ℕ) : Continuous (primePhase j p) := by
  unfold primePhase
  apply continuous_finset_sum
  intro n _
  exact continuous_const.mul (P_continuous.comp (continuous_const.mul continuous_id))

/-- The actual remaining C12 lower bounds need only be checked on one
closed compact period. No particular positive J_p values are asserted. -/
def CompactPhaseCertificate (j : Fin 7) (Jp : ℕ → ℝ) : Prop :=
  ∀ p ∈ selectedPrimes j, ∀ x ∈ Set.Icc (0 : ℝ) (2 * Real.pi), Jp p ≤ primePhase j p x

@[blueprint "varlamov-compact-phase-certificate"
  (title := "Varlamov, C12: reduction to a single compact period")
  (statement := /-- The global prime-phase certificate is equivalent to the
  lower bound on $[0,2\pi]$. Periodicity and continuity of the actual phase
  function are proved. Numerical cell bounds remain unproved. -/)
  (uses := ["varlamov-prime-weights", "varlamov-prime-lifting"])]
theorem phase_certificate_iff_compact (j : Fin 7) (Jp : ℕ → ℝ) :
    PrimePhaseCertificate j Jp ↔ CompactPhaseCertificate j Jp := by
  constructor
  · intro h p hp x _
    exact h p hp x
  · intro h p hp x
    obtain ⟨y,hy,he⟩ := (primePhase_periodic j p).exists_mem_Ico₀ (by positivity : 0 < 2 * Real.pi) x
    rw [he]
    exact h p hp y ⟨hy.1,hy.2.le⟩

/-- This is the conditional target with exactly the two still unproved
compact numerical certificate obligations. It is NOT an unconditional proof
of the new R=4.81406 region. -/
theorem zeroFreeRegion_of_compact_certificates
    (hK : KadiriInput) (hPT : PlattTrudgianInput) (hY : YangInput)
    (hK2 : KadiriExplicitInput) (hK3 : KadiriDigammaInput) (hC : HalfPlaneCauchyInput)
    (hL1 : LehmanMonotoneInput) (hL2 : LehmanSquareTailInput)
    (Jp : Fin 7 → ℕ → ℝ)
    (hPhase : ∀ j : Fin 7, CompactPhaseCertificate j (Jp j))
    (hMargin : MarginCertificate Jp) : ZeroFreeRegion :=
  zeroFreeRegion_of_finite_certificates hK hPT hY hK2 hK3 hC hL1 hL2 Jp
    (fun j => (phase_certificate_iff_compact j (Jp j)).mpr (hPhase j)) hMargin

#print axioms zeroFreeRegion_of_compact_certificates
end Varlamov
