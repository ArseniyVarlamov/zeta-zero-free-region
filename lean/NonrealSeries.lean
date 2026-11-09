import PrimeNumberTheoremAnd.IEANTN.Varlamov.RemainderBounds
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace Varlamov.Kernel
open Real MeasureTheory
open scoped BigOperators

noncomputable def heightMajorant (τ x : ℝ) : ℝ :=
  1 / (Real.sqrt ((2 * x) ^ 2 + τ ^ 2)) ^ 3
noncomputable def heightPrimitive (τ x : ℝ) : ℝ :=
  x / (τ ^ 2 * Real.sqrt ((2 * x) ^ 2 + τ ^ 2))

lemma heightPrimitive_hasDerivAt {τ : ℝ} (hτ : 0 < τ) (x : ℝ) :
    HasDerivAt (heightPrimitive τ) (heightMajorant τ x) x := by
  have hpos : 0 < (2 * x) ^ 2 + τ ^ 2 := by positivity
  have hr : 0 < Real.sqrt ((2 * x) ^ 2 + τ ^ 2) := Real.sqrt_pos.mpr hpos
  have hd := ((((hasDerivAt_id x).const_mul 2).pow 2).add_const (τ ^ 2)).sqrt (ne_of_gt hpos)
  have hq := (hasDerivAt_id x).div (hd.const_mul (τ ^ 2)) (by positivity : τ ^ 2 * Real.sqrt ((2 * x) ^ 2 + τ ^ 2) ≠ 0)
  convert hq using 1
  · rfl
  · dsimp [heightMajorant]
    field_simp
    have hs := Real.sq_sqrt hpos.le
    ring_nf at hs ⊢
    nlinarith [hs]

/-- Exact integral comparison underlying the nonreal case of Lemma 6.4. -/
lemma height_progression_bound {τ : ℝ} (hτ : 0 < τ) :
    Summable (fun n : ℕ => heightMajorant τ n) ∧
      (∑' n : ℕ, heightMajorant τ n) ≤ 1 / τ ^ 3 + 1 / (2 * τ ^ 2) := by
  have hnonneg (x : ℝ) : 0 ≤ heightMajorant τ x := by unfold heightMajorant; positivity
  have hanti : AntitoneOn (heightMajorant τ) (Set.Ici 0) := by
    intro x hx y hy hxy
    change 0 ≤ x at hx
    change 0 ≤ y at hy
    unfold heightMajorant
    gcongr
  have hbound (N : ℕ) : (∫ x in (0 : ℝ)..N, heightMajorant τ x) ≤ 1 / (2 * τ ^ 2) := by
    have hc : Continuous (heightMajorant τ) := by
      apply Continuous.div continuous_const
      · exact (Real.continuous_sqrt.comp (by fun_prop)).pow 3
      · intro x
        exact pow_ne_zero 3 (ne_of_gt (Real.sqrt_pos.mpr (by positivity)))
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => heightPrimitive_hasDerivAt hτ x) (hc.intervalIntegrable 0 N)]
    simp only [heightPrimitive, zero_div, sub_zero]
    have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
    have hs : 2 * (N : ℝ) ≤ Real.sqrt ((2 * (N : ℝ)) ^ 2 + τ ^ 2) := by
      apply (Real.le_sqrt (by positivity) (by positivity)).mpr
      nlinarith [sq_nonneg τ]
    have hr : 0 < Real.sqrt ((2 * (N : ℝ)) ^ 2 + τ ^ 2) := Real.sqrt_pos.mpr (by positivity)
    apply (div_le_div_iff₀ (by positivity : 0 < τ ^ 2 * Real.sqrt ((2 * (N : ℝ)) ^ 2 + τ ^ 2)) (by positivity : 0 < 2 * τ ^ 2)).mpr
    nlinarith
  have hb (N : ℕ) : (∑ n ∈ Finset.range N, heightMajorant τ n) ≤ 1 / τ ^ 3 + 1 / (2 * τ ^ 2) := by
    cases N with
    | zero => simp only [Finset.sum_range_zero]; positivity
    | succ N =>
      rw [Finset.sum_range_succ']
      have ha : AntitoneOn (heightMajorant τ) (Set.Icc 0 (0 + (N : ℝ))) :=
        hanti.mono (by intro x hx; exact hx.1)
      have hi := ha.sum_le_integral
      simp only [zero_add] at hi
      have hz : heightMajorant τ 0 = 1 / τ ^ 3 := by
        simp [heightMajorant, Real.sqrt_sq hτ.le]
      simp only [Nat.cast_zero, hz]
      linarith [hbound N]
  exact ⟨summable_of_sum_range_le (fun n => hnonneg n) hb,
    Real.tsum_le_of_sum_range_le (fun n => hnonneg n) hb⟩

/-- The nonreal part of Lemma 6.4, with the exact article constant. -/
theorem Delta_height_bound (hC : HalfPlaneCauchyInput) {η ηmax u T : ℝ} {s : ℂ}
    (hη : 0 < η) (hηmax : η ≤ ηmax) (hs : (1 / 2 : ℝ) < s.re)
    (hu : 0 < u) (hsu : u ≤ s.re + 2) (hT : 0 < T) (him : T ≤ |s.im|) :
    ‖Delta η s‖ ≤ C (u / ηmax) * η ^ 3 * (1 / T ^ 3 + 1 / (2 * T ^ 2)) := by
  let P := C (u / ηmax) * η ^ 3
  have hP : 0 ≤ P := mul_nonneg (C_pos (div_pos hu (hη.trans_le hηmax))).le (by positivity)
  have hb (n : ℕ) : ‖zeroSample η s (n + 1)‖ ≤ P * heightMajorant T n := by
    let v : ℂ := s + 2 * ((n + 1 : ℕ) : ℂ)
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hre : 2 * (n : ℝ) ≤ v.re := by
      simp [v]
      
      linarith
    have him' : T ≤ |v.im| := by simpa [v] using him
    have hsq : (2 * (n : ℝ)) ^ 2 + T ^ 2 ≤ ‖v‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      have hx : (2 * (n : ℝ)) ^ 2 ≤ v.re ^ 2 := by nlinarith
      have hy : T ^ 2 ≤ v.im ^ 2 := by nlinarith [sq_abs v.im, abs_nonneg v.im]
      linarith
    have hroot : Real.sqrt ((2 * (n : ℝ)) ^ 2 + T ^ 2) ≤ ‖v‖ :=
      (Real.sqrt_le_iff).mpr ⟨norm_nonneg _, hsq⟩
    calc
      _ ≤ P / ‖v‖ ^ 3 := zeroSample_succ_bound hη hηmax hu hsu n
      _ ≤ P / (Real.sqrt ((2 * (n : ℝ)) ^ 2 + T ^ 2)) ^ 3 := by gcongr
      _ = _ := by dsimp [heightMajorant]; ring
  have hsum := height_progression_bound hT
  have hnorm := (Delta_trivial_zeros hC hη hs).1
  rw [(Delta_trivial_zeros hC hη hs).2, norm_neg]
  calc
    _ ≤ ∑' n : ℕ, ‖zeroSample η s (n + 1)‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' n : ℕ, P * heightMajorant T n := hnorm.tsum_le_tsum hb (hsum.1.mul_left P)
    _ = P * (∑' n : ℕ, heightMajorant T n) := tsum_mul_left
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum.2 hP

#print axioms Delta_height_bound
end Varlamov.Kernel
