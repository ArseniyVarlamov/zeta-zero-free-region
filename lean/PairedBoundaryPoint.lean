import PrimeNumberTheoremAnd.IEANTN.Varlamov.PairChecks

namespace Varlamov
open Real

/-- The common-scale boundary estimate for each m>=1. This keeps the same
rational denominator for positive and negative multiplier coefficients. -/
theorem boundary_point_error (j : Fin 7) {h η m y : ℝ}
    (hh : hMin j ≤ h) (hη : 0 < η) (hηmax : η ≤ etaMax j) (hm : 1 ≤ m) :
    |(Kernel.W ((((h * m : ℝ) : ℂ) + (y : ℂ) * Complex.I) / (η : ℂ))).re -
      (10 * η / h) * m / (m ^ 2 + (y / h) ^ 2)| ≤
        (10 * η / h) * pairedEps j / (m * (m ^ 2 + (y / h) ^ 2)) := by
  have hh0 : 0 < h := (hMin_pos j).trans_le hh
  have hm0 : 0 < m := by linarith
  have hε : 0 < pairedEps j := (pairedEps_range j).1
  have hη0 : η ≠ 0 := ne_of_gt hη
  have hhne : h ≠ 0 := ne_of_gt hh0
  let ζ : ℂ := (((h * m : ℝ) : ℂ) + (y : ℂ) * Complex.I) / (η : ℂ)
  let D : ℝ := m ^ 2 + (y / h) ^ 2
  have hD : 0 < D := by dsimp [D]; positivity
  have hre : ζ.re = h * m / η := by simp [ζ]
  have him : ζ.im = y / η := by simp [ζ]
  have hν : nuMin j ≤ ζ.re := by
    rw [hre]
    calc
      nuMin j ≤ hMin j / η := div_le_div_of_nonneg_left (hMin_pos j).le hη hηmax
      _ ≤ h / η := div_le_div_of_nonneg_right hh hη.le
      _ ≤ h * m / η := div_le_div_of_nonneg_right (by nlinarith) hη.le
  have hnorm : 0 < ‖ζ‖ := lt_of_lt_of_le (nuMin_pos j)
    (hν.trans (Complex.re_le_norm ζ))
  have hnormsq : ‖ζ‖ ^ 2 = h ^ 2 * D / η ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    rw [hre, him]
    dsimp [D]
    field_simp
    
  have hlinear : h * m / η ≤ ‖ζ‖ := by rw [← hre]; exact Complex.re_le_norm ζ
  have hcube : h ^ 3 * m * D / η ^ 3 ≤ ‖ζ‖ ^ 3 := by
    calc
      _ = (h * m / η) * ‖ζ‖ ^ 2 := by rw [hnormsq]; ring
      _ ≤ ‖ζ‖ * ‖ζ‖ ^ 2 := mul_le_mul_of_nonneg_right hlinear (sq_nonneg ‖ζ‖)
      _ = ‖ζ‖ ^ 3 := by ring
  have hlower : 0 < h ^ 3 * m * D / η ^ 3 := by positivity
  have hbudget := (pair_error_bound j hh hη hηmax).le
  have hfrac : Kernel.C (nuMin j) ≤ 10 * pairedEps j * h ^ 2 / η ^ 2 := by
    apply (le_div_iff₀ (pow_pos hη 2)).mpr
    nlinarith
  have hfrac0 : 0 ≤ 10 * pairedEps j * h ^ 2 / η ^ 2 := by positivity
  have herr : Kernel.C (nuMin j) / ‖ζ‖ ^ 3 ≤ (10 * η / h) * pairedEps j / (m * D) := by
    calc
      _ ≤ (10 * pairedEps j * h ^ 2 / η ^ 2) / ‖ζ‖ ^ 3 :=
        div_le_div_of_nonneg_right hfrac (by positivity)
      _ ≤ (10 * pairedEps j * h ^ 2 / η ^ 2) / (h ^ 3 * m * D / η ^ 3) :=
        div_le_div_of_nonneg_left hfrac0 hlower hcube
      _ = _ := by field_simp
  have hden : (h * m) * (h * m) + y * y ≠ 0 := by
    nlinarith [sq_pos_of_pos (mul_pos hh0 hm0), sq_nonneg y]
  have hmain : ((10 : ℂ) / ζ).re = (10 * η / h) * m / D := by
    dsimp [ζ]
    rw [div_div_eq_mul_div]
    simp only [Complex.div_re, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, zero_mul, mul_zero, one_mul, mul_one, add_zero,
      zero_add, sub_zero, Complex.re_ofNat, Complex.im_ofNat]
    dsimp [D]
    field_simp
    ring
  have hrem : |(Kernel.W ζ).re - ((10 : ℂ) / ζ).re| ≤
      Kernel.C (nuMin j) / ‖ζ‖ ^ 3 := by
    have h := Complex.abs_re_le_norm (Kernel.W ζ - 10 / ζ)
    simp only [Complex.sub_re] at h
    exact h.trans (Kernel.W_right_bound (nuMin_pos j) hν)
  rw [hmain] at hrem
  exact hrem.trans herr

#print axioms boundary_point_error

end Varlamov
