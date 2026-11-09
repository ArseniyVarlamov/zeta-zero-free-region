import PrimeNumberTheoremAnd.IEANTN.Varlamov.Multipliers

namespace Varlamov.Multiplier
open Real
open scoped BigOperators

def length (j : Fin 7) : ℕ := if j.val = 6 then 15 else 11

noncomputable def coefficient (j : Fin 7) (m : ℕ) : ℝ :=
  match j.val with
  | 0 => coefficient1 m
  | 1 => coefficient2 m
  | 2 => coefficient3 m
  | 3 => coefficient4 m
  | 4 => coefficient5 m
  | 5 => coefficient6 m
  | _ => coefficient7 m

noncomputable def kappa (j : Fin 7) (x : ℝ) : ℝ :=
  match j.val with
  | 0 => kappa1 x
  | 1 => kappa2 x
  | 2 => kappa3 x
  | 3 => kappa4 x
  | 4 => kappa5 x
  | 5 => kappa6 x
  | _ => kappa7 x

noncomputable def pair (j : Fin 7) (Y : ℝ) : ℝ :=
  match j.val with
  | 0 => pair1 Y
  | 1 => pair2 Y
  | 2 => pair3 Y
  | 3 => pair4 Y
  | 4 => pair5 Y
  | 5 => pair6 Y
  | _ => pair7 Y

noncomputable def coeffNorm (j : Fin 7) : ℝ :=
  ∑ m ∈ Finset.range (length j), |coefficient j m|

lemma length_pos (j : Fin 7) : 0 < length j := by unfold length; split_ifs <;> norm_num
lemma coefficient_zero (j : Fin 7) : coefficient j 0 = 1 := by fin_cases j <;> rfl
lemma coefficient_end (j : Fin 7) : coefficient j (length j) = 0 := by fin_cases j <;> rfl
lemma coeffNorm_nonneg (j : Fin 7) : 0 ≤ coeffNorm j := Finset.sum_nonneg (fun _ _ => abs_nonneg _)

lemma kappa_sum (j : Fin 7) (x : ℝ) :
    kappa j x = ∑ m ∈ Finset.range (length j), coefficient j m * x ^ m := by
  fin_cases j
  · exact kappa1_sum x
  · exact kappa2_sum x
  · exact kappa3_sum x
  · exact kappa4_sum x
  · exact kappa5_sum x
  · exact kappa6_sum x
  · exact kappa7_sum x

lemma kappa_pos (j : Fin 7) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) : 0 < kappa j x := by
  fin_cases j
  · exact kappa1_pos x hx
  · exact kappa2_pos x hx
  · exact kappa3_pos x hx
  · exact kappa4_pos x hx
  · exact kappa5_pos x hx
  · exact kappa6_pos x hx
  · exact kappa7_pos x hx

lemma kappa_strictAnti (j : Fin 7) : StrictAntiOn (kappa j) (Set.Icc (0 : ℝ) 1) := by
  fin_cases j
  · exact kappa1_strictAnti
  · exact kappa2_strictAnti
  · exact kappa3_strictAnti
  · exact kappa4_strictAnti
  · exact kappa5_strictAnti
  · exact kappa6_strictAnti
  · exact kappa7_strictAnti

lemma pair_from_coefficients (j : Fin 7) (Y : ℝ) :
    pair j Y = ∑ m ∈ Finset.range (length j),
      (((m + 1 : ℝ) * (coefficient j (m + 1) + coefficient j m) -
        pairedEps j * |coefficient j (m + 1) + coefficient j m| / (m + 1)) /
          ((m + 1 : ℝ) ^ 2 + Y)) := by
  fin_cases j
  · exact pair1_from_coefficients Y
  · exact pair2_from_coefficients Y
  · exact pair3_from_coefficients Y
  · exact pair4_from_coefficients Y
  · exact pair5_from_coefficients Y
  · exact pair6_from_coefficients Y
  · exact pair7_from_coefficients Y

lemma pair_pos (j : Fin 7) {Y : ℝ} (hY : 0 ≤ Y) : 0 < pair j Y := by
  fin_cases j
  · exact pair1_pos Y hY
  · exact pair2_pos Y hY
  · exact pair3_pos Y hY
  · exact pair4_pos Y hY
  · exact pair5_pos Y hY
  · exact pair6_pos Y hY
  · exact pair7_pos Y hY

#print axioms pair_from_coefficients
#print axioms pair_pos

end Varlamov.Multiplier
