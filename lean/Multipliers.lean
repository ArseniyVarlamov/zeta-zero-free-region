import PrimeNumberTheoremAnd.IEANTN.Varlamov.Bands
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.FunProp

/-! # Exact multiplier and paired rational-function certificates

The coefficients are transcribed from parameters.json. Every polynomial identity
and every bound below is checked in Lean; the generator is not a trusted checker.
The positive-half-line Sturm checks C6 are replaced by Bernstein certificates
on x=Y/(Y+10) in [0,1], including both endpoints.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace Varlamov
namespace Multiplier
open Real
open scoped BigOperators

noncomputable def kappa1 (x : ℝ) : ℝ :=
  (1) +
    ((-999856412099 / 1000000000000 : ℝ)) * x +
    ((498101115981 / 500000000000 : ℝ)) * x ^ 2 +
    ((-60276831517 / 62500000000 : ℝ)) * x ^ 3 +
    ((104047332287 / 125000000000 : ℝ)) * x ^ 4 +
    ((-269232895919 / 500000000000 : ℝ)) * x ^ 5 +
    ((37624103377 / 200000000000 : ℝ)) * x ^ 6 +
    ((-12122941721 / 500000000000 : ℝ)) * x ^ 9 +
    ((10310013107 / 1000000000000 : ℝ)) * x ^ 10

noncomputable def coefficient1 (m : ℕ) : ℝ :=
  match m with
  | 0 => 1
  | 1 => (-999856412099 / 1000000000000 : ℝ)
  | 2 => (498101115981 / 500000000000 : ℝ)
  | 3 => (-60276831517 / 62500000000 : ℝ)
  | 4 => (104047332287 / 125000000000 : ℝ)
  | 5 => (-269232895919 / 500000000000 : ℝ)
  | 6 => (37624103377 / 200000000000 : ℝ)
  | 7 => 0
  | 8 => 0
  | 9 => (-12122941721 / 500000000000 : ℝ)
  | 10 => (10310013107 / 1000000000000 : ℝ)
  | _ => 0

lemma kappa1_sum (x : ℝ) :
    kappa1 x = ∑ m ∈ Finset.range 11, coefficient1 m * x ^ m := by
  norm_num [kappa1, coefficient1, Finset.sum_range_succ] 

lemma horizontal1_pos :
    0 < ∑ m ∈ Finset.range 11, (2 * m + 1 : ℝ) * coefficient1 m := by
  norm_num [coefficient1, Finset.sum_range_succ]

noncomputable def kappa1Derivative (x : ℝ) : ℝ :=
  ((-999856412099 / 1000000000000 : ℝ)) +
    ((498101115981 / 250000000000 : ℝ)) * x +
    ((-180830494551 / 62500000000 : ℝ)) * x ^ 2 +
    ((104047332287 / 31250000000 : ℝ)) * x ^ 3 +
    ((-269232895919 / 100000000000 : ℝ)) * x ^ 4 +
    ((112872310131 / 100000000000 : ℝ)) * x ^ 5 +
    ((-109106475489 / 500000000000 : ℝ)) * x ^ 8 +
    ((10310013107 / 100000000000 : ℝ)) * x ^ 9

lemma kappa1_zero : kappa1 0 = 1 := by norm_num [kappa1]
lemma kappa1_pos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < kappa1 x := by
  unfold kappa1
  bernstein_bound (trust := kernel)
lemma kappa1_deriv_neg : ∀ x ∈ Set.Icc (0 : ℝ) 1, kappa1Derivative x < 0 := by
  unfold kappa1Derivative
  bernstein_bound (trust := kernel)
lemma kappa1_hasDerivAt (x : ℝ) : HasDerivAt kappa1 (kappa1Derivative x) x := by
  unfold kappa1 kappa1Derivative
  convert (((((((((hasDerivAt_const x (1)).add (((hasDerivAt_id x).pow 1).const_mul ((-999856412099 / 1000000000000 : ℝ)))).add (((hasDerivAt_id x).pow 2).const_mul ((498101115981 / 500000000000 : ℝ)))).add (((hasDerivAt_id x).pow 3).const_mul ((-60276831517 / 62500000000 : ℝ)))).add (((hasDerivAt_id x).pow 4).const_mul ((104047332287 / 125000000000 : ℝ)))).add (((hasDerivAt_id x).pow 5).const_mul ((-269232895919 / 500000000000 : ℝ)))).add (((hasDerivAt_id x).pow 6).const_mul ((37624103377 / 200000000000 : ℝ)))).add (((hasDerivAt_id x).pow 9).const_mul ((-12122941721 / 500000000000 : ℝ)))).add (((hasDerivAt_id x).pow 10).const_mul ((10310013107 / 1000000000000 : ℝ)))) using 1 <;> (try funext y) <;> dsimp <;> ring
lemma kappa1_strictAnti : StrictAntiOn kappa1 (Set.Icc (0 : ℝ) 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc 0 1)
    (fun x _ => (kappa1_hasDerivAt x).continuousAt.continuousWithinAt)
  intro x hx
  rw [(kappa1_hasDerivAt x).deriv]
  exact kappa1_deriv_neg x (interior_subset hx)

noncomputable def pair1 (Y : ℝ) : ℝ :=
  ((3587950203832731 / 25000000000000000000 : ℝ)) / (1 + Y) +
    ((-365462481418087153 / 50000000000000000000 : ℝ)) / (4 + Y) +
    ((714852208549294039 / 7500000000000000000 : ℝ)) / (9 + Y) +
    ((-6602733164338860243 / 12500000000000000000 : ℝ)) / (16 + Y) +
    ((91845982455289036299 / 62500000000000000000 : ℝ)) / (25 + Y) +
    ((-315315010809350903057 / 150000000000000000000 : ℝ)) / (36 + Y) +
    ((6584152684158715041 / 5000000000000000000 : ℝ)) / (49 + Y) +
    ((-24549104509102802849 / 112500000000000000000 : ℝ)) / (81 + Y) +
    ((-6967969084621221323 / 50000000000000000000 : ℝ)) / (100 + Y) +
    ((31187664186125500917 / 275000000000000000000 : ℝ)) / (121 + Y)

lemma pair1_from_coefficients (Y : ℝ) :
    pair1 Y = ∑ m ∈ Finset.range 11,
      (((m + 1 : ℝ) * (coefficient1 (m + 1) + coefficient1 m) -
        pairedEps ⟨0, by decide⟩ * |coefficient1 (m + 1) + coefficient1 m| / (m + 1)) /
          ((m + 1 : ℝ) ^ 2 + Y)) := by
  norm_num [pair1, coefficient1, pairedEps, Finset.sum_range_succ] 

noncomputable def numerator1 (Y : ℝ) : ℝ :=
  (255094166194959487050114217574400) +
    (-1113534328673747639680811211096576) * Y +
    (1398139559500350645825784419751984) * Y ^ 2 +
    (-301860603533054263263365442219016) * Y ^ 3 +
    (18488042264685806736371738113219) * Y ^ 4 +
    (2772202090241218048239265904) * Y ^ 5 +
    (-7471350579949218139153252661) * Y ^ 6 +
    (23553058210012700223904544) * Y ^ 7 +
    (700605077386732374178729) * Y ^ 8 +
    (-1486779233120490054856) * Y ^ 9 +
    (778908419941034329) * Y ^ 10

noncomputable def compact1 (x : ℝ) : ℝ :=
  (255094166194959487050114217574400) +
    (-13686284948687071267309254286709760) * x +
    (251511283009445529071106590764738240) * x ^ 2 +
    (-1851855909399279068655098720124298560) * x ^ 3 +
    (7201634024966109228131877254982605040) * x ^ 4 +
    (-16744996507078279244266998306223620960) * x ^ 5 +
    (24573069957267018436569115358971607760) * x ^ 6 +
    (-23025398110833229116287334652362522240) * x ^ 7 +
    (13391184539490816439848520509383356560) * x ^ 8 +
    (-4411750952138888250505704891186275040) * x ^ 9 +
    (630032873287862357285119285863544560) * x ^ 10

lemma compact1_pos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < compact1 x := by
  unfold compact1
  bernstein_bound 10 (trust := kernel)

lemma compact1_identity (Y : ℝ) (hY : 0 ≤ Y) :
    (Y + 10) ^ 10 * compact1 (Y / (Y + 10)) = 10 ^ 10 * numerator1 Y := by
  have h : Y + 10 ≠ 0 := by linarith
  unfold compact1 numerator1
  field_simp
  ring

lemma numerator1_pos (Y : ℝ) (hY : 0 ≤ Y) : 0 < numerator1 Y := by
  have hd : 0 < Y + 10 := by linarith
  have hx : Y / (Y + 10) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg hY hd.le
    · exact (div_le_one hd).mpr (by linarith)
  have hp := mul_pos (pow_pos hd 10) (compact1_pos _ hx)
  rw [compact1_identity Y hY] at hp
  exact (mul_pos_iff_of_pos_left (by norm_num : (0 : ℝ) < 10 ^ 10)).mp hp

lemma pair1_identity (Y : ℝ) (hY : 0 ≤ Y) :
    (24750000000000000000000) * pair1 Y * ((1 + Y) * (4 + Y) * (9 + Y) * (16 + Y) * (25 + Y) * (36 + Y) * (49 + Y) * (64 + Y) * (81 + Y) * (100 + Y) * (121 + Y)) = numerator1 Y := by
  have h1 : (1 : ℝ) + Y ≠ 0 := by linarith
  have h2 : (4 : ℝ) + Y ≠ 0 := by linarith
  have h3 : (9 : ℝ) + Y ≠ 0 := by linarith
  have h4 : (16 : ℝ) + Y ≠ 0 := by linarith
  have h5 : (25 : ℝ) + Y ≠ 0 := by linarith
  have h6 : (36 : ℝ) + Y ≠ 0 := by linarith
  have h7 : (49 : ℝ) + Y ≠ 0 := by linarith
  have h8 : (64 : ℝ) + Y ≠ 0 := by linarith
  have h9 : (81 : ℝ) + Y ≠ 0 := by linarith
  have h10 : (100 : ℝ) + Y ≠ 0 := by linarith
  have h11 : (121 : ℝ) + Y ≠ 0 := by linarith
  unfold pair1 numerator1
  field_simp
  ring

lemma pair1_pos (Y : ℝ) (hY : 0 ≤ Y) : 0 < pair1 Y := by
  have hp := numerator1_pos Y hY
  rw [← pair1_identity Y hY] at hp
  have hd : 0 < ((1 + Y) * (4 + Y) * (9 + Y) * (16 + Y) * (25 + Y) * (36 + Y) * (49 + Y) * (64 + Y) * (81 + Y) * (100 + Y) * (121 + Y) : ℝ) := by positivity
  have hs : (0 : ℝ) < 24750000000000000000000 := by norm_num
  have hm : 0 < (24750000000000000000000) * pair1 Y := (mul_pos_iff_of_pos_right hd).mp hp
  exact (mul_pos_iff_of_pos_left hs).mp hm

#print axioms pair1_pos

noncomputable def kappa2 (x : ℝ) : ℝ :=
  (1) +
    ((-999908741467 / 1000000000000 : ℝ)) * x +
    ((997343300509 / 1000000000000 : ℝ)) * x ^ 2 +
    ((-97299986547 / 100000000000 : ℝ)) * x ^ 3 +
    ((53931226707 / 62500000000 : ℝ)) * x ^ 4 +
    ((-594616405027 / 1000000000000 : ℝ)) * x ^ 5 +
    ((58981084521 / 250000000000 : ℝ)) * x ^ 6 +
    ((-16637693377 / 500000000000 : ℝ)) * x ^ 8 +
    ((2320029937 / 500000000000 : ℝ)) * x ^ 10

noncomputable def coefficient2 (m : ℕ) : ℝ :=
  match m with
  | 0 => 1
  | 1 => (-999908741467 / 1000000000000 : ℝ)
  | 2 => (997343300509 / 1000000000000 : ℝ)
  | 3 => (-97299986547 / 100000000000 : ℝ)
  | 4 => (53931226707 / 62500000000 : ℝ)
  | 5 => (-594616405027 / 1000000000000 : ℝ)
  | 6 => (58981084521 / 250000000000 : ℝ)
  | 7 => 0
  | 8 => (-16637693377 / 500000000000 : ℝ)
  | 9 => 0
  | 10 => (2320029937 / 500000000000 : ℝ)
  | _ => 0

lemma kappa2_sum (x : ℝ) :
    kappa2 x = ∑ m ∈ Finset.range 11, coefficient2 m * x ^ m := by
  norm_num [kappa2, coefficient2, Finset.sum_range_succ] 

lemma horizontal2_pos :
    0 < ∑ m ∈ Finset.range 11, (2 * m + 1 : ℝ) * coefficient2 m := by
  norm_num [coefficient2, Finset.sum_range_succ]

noncomputable def kappa2Derivative (x : ℝ) : ℝ :=
  ((-999908741467 / 1000000000000 : ℝ)) +
    ((997343300509 / 500000000000 : ℝ)) * x +
    ((-291899959641 / 100000000000 : ℝ)) * x ^ 2 +
    ((53931226707 / 15625000000 : ℝ)) * x ^ 3 +
    ((-594616405027 / 200000000000 : ℝ)) * x ^ 4 +
    ((176943253563 / 125000000000 : ℝ)) * x ^ 5 +
    ((-16637693377 / 62500000000 : ℝ)) * x ^ 7 +
    ((2320029937 / 50000000000 : ℝ)) * x ^ 9

lemma kappa2_zero : kappa2 0 = 1 := by norm_num [kappa2]
lemma kappa2_pos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < kappa2 x := by
  unfold kappa2
  bernstein_bound (trust := kernel)
lemma kappa2_deriv_neg : ∀ x ∈ Set.Icc (0 : ℝ) 1, kappa2Derivative x < 0 := by
  unfold kappa2Derivative
  bernstein_bound (trust := kernel)
lemma kappa2_hasDerivAt (x : ℝ) : HasDerivAt kappa2 (kappa2Derivative x) x := by
  unfold kappa2 kappa2Derivative
  convert (((((((((hasDerivAt_const x (1)).add (((hasDerivAt_id x).pow 1).const_mul ((-999908741467 / 1000000000000 : ℝ)))).add (((hasDerivAt_id x).pow 2).const_mul ((997343300509 / 1000000000000 : ℝ)))).add (((hasDerivAt_id x).pow 3).const_mul ((-97299986547 / 100000000000 : ℝ)))).add (((hasDerivAt_id x).pow 4).const_mul ((53931226707 / 62500000000 : ℝ)))).add (((hasDerivAt_id x).pow 5).const_mul ((-594616405027 / 1000000000000 : ℝ)))).add (((hasDerivAt_id x).pow 6).const_mul ((58981084521 / 250000000000 : ℝ)))).add (((hasDerivAt_id x).pow 8).const_mul ((-16637693377 / 500000000000 : ℝ)))).add (((hasDerivAt_id x).pow 10).const_mul ((2320029937 / 500000000000 : ℝ)))) using 1 <;> (try funext y) <;> dsimp <;> ring
lemma kappa2_strictAnti : StrictAntiOn kappa2 (Set.Icc (0 : ℝ) 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc 0 1)
    (fun x _ => (kappa2_hasDerivAt x).continuousAt.continuousWithinAt)
  intro x hx
  rw [(kappa2_hasDerivAt x).deriv]
  exact kappa2_deriv_neg x (interior_subset hx)

noncomputable def pair2 (Y : ℝ) : ℝ :=
  ((1824814112911569 / 20000000000000000000 : ℝ)) / (1 + Y) +
    ((-102622649908911453 / 20000000000000000000 : ℝ)) / (4 + Y) +
    ((4381723197219302627 / 60000000000000000000 : ℝ)) / (9 + Y) +
    ((-17616253186095241653 / 40000000000000000000 : ℝ)) / (16 + Y) +
    ((26828112591990106501 / 20000000000000000000 : ℝ)) / (25 + Y) +
    ((-258259689608865546301 / 120000000000000000000 : ℝ)) / (36 + Y) +
    ((57801232391482776453 / 35000000000000000000 : ℝ)) / (49 + Y) +
    ((-21296312526028023939 / 80000000000000000000 : ℝ)) / (64 + Y) +
    ((-26953128274208023939 / 90000000000000000000 : ℝ)) / (81 + Y) +
    ((4640050809643036141 / 100000000000000000000 : ℝ)) / (100 + Y) +
    ((5614463383183036141 / 110000000000000000000 : ℝ)) / (121 + Y)

lemma pair2_from_coefficients (Y : ℝ) :
    pair2 Y = ∑ m ∈ Finset.range 11,
      (((m + 1 : ℝ) * (coefficient2 (m + 1) + coefficient2 m) -
        pairedEps ⟨1, by decide⟩ * |coefficient2 (m + 1) + coefficient2 m| / (m + 1)) /
          ((m + 1 : ℝ) ^ 2 + Y)) := by
  norm_num [pair2, coefficient2, pairedEps, Finset.sum_range_succ] 

noncomputable def numerator2 (Y : ℝ) : ℝ :=
  (1640475016842275768561621547340800) +
    (-7487099149342965959423381452573248) * Y +
    (10180048863021423322886070761727472) * Y ^ 2 +
    (-2489443629482926686418275720757948) * Y ^ 3 +
    (182818053867652472807459882953597) * Y ^ 4 +
    (-1406033804262969006080955144418) * Y ^ 5 +
    (-66681685284963401915541437873) * Y ^ 6 +
    (543066866844800589336497672) * Y ^ 7 +
    (6287076542360874321513067) * Y ^ 8 +
    (-18628029827991530202058) * Y ^ 9 +
    (12697239131579322937) * Y ^ 10

noncomputable def compact2 (x : ℝ) : ℝ :=
  (1640475016842275768561621547340800) +
    (-91275741661852417279850029999140480) * x +
    (1765665185500911678221984376534675520) * x ^ 2 +
    (-13525695415684606182346944238747190880) * x ^ 3 +
    (54392085800501966154397107952781623920) * x ^ 4 +
    (-130243421096963266894552464153420545280) * x ^ 5 +
    (196228157051755804327357465291179894480) * x ^ 6 +
    (-188322308120276731084962082504969847520) * x ^ 7 +
    (111964618579472767459301223898070084880) * x ^ 8 +
    (-37650745600790650569810821740065433920) * x ^ 9 +
    (5481279010101206569699048897088538480) * x ^ 10

lemma compact2_pos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < compact2 x := by
  unfold compact2
  bernstein_bound 10 (trust := kernel)

lemma compact2_identity (Y : ℝ) (hY : 0 ≤ Y) :
    (Y + 10) ^ 10 * compact2 (Y / (Y + 10)) = 10 ^ 10 * numerator2 Y := by
  have h : Y + 10 ≠ 0 := by linarith
  unfold compact2 numerator2
  field_simp
  ring

lemma numerator2_pos (Y : ℝ) (hY : 0 ≤ Y) : 0 < numerator2 Y := by
  have hd : 0 < Y + 10 := by linarith
  have hx : Y / (Y + 10) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg hY hd.le
    · exact (div_le_one hd).mpr (by linarith)
  have hp := mul_pos (pow_pos hd 10) (compact2_pos _ hx)
  rw [compact2_identity Y hY] at hp
  exact (mul_pos_iff_of_pos_left (by norm_num : (0 : ℝ) < 10 ^ 10)).mp hp

lemma pair2_identity (Y : ℝ) (hY : 0 ≤ Y) :
    (277200000000000000000000) * pair2 Y * ((1 + Y) * (4 + Y) * (9 + Y) * (16 + Y) * (25 + Y) * (36 + Y) * (49 + Y) * (64 + Y) * (81 + Y) * (100 + Y) * (121 + Y)) = numerator2 Y := by
  have h1 : (1 : ℝ) + Y ≠ 0 := by linarith
  have h2 : (4 : ℝ) + Y ≠ 0 := by linarith
  have h3 : (9 : ℝ) + Y ≠ 0 := by linarith
  have h4 : (16 : ℝ) + Y ≠ 0 := by linarith
  have h5 : (25 : ℝ) + Y ≠ 0 := by linarith
  have h6 : (36 : ℝ) + Y ≠ 0 := by linarith
  have h7 : (49 : ℝ) + Y ≠ 0 := by linarith
  have h8 : (64 : ℝ) + Y ≠ 0 := by linarith
  have h9 : (81 : ℝ) + Y ≠ 0 := by linarith
  have h10 : (100 : ℝ) + Y ≠ 0 := by linarith
  have h11 : (121 : ℝ) + Y ≠ 0 := by linarith
  unfold pair2 numerator2
  field_simp
  ring

lemma pair2_pos (Y : ℝ) (hY : 0 ≤ Y) : 0 < pair2 Y := by
  have hp := numerator2_pos Y hY
  rw [← pair2_identity Y hY] at hp
  have hd : 0 < ((1 + Y) * (4 + Y) * (9 + Y) * (16 + Y) * (25 + Y) * (36 + Y) * (49 + Y) * (64 + Y) * (81 + Y) * (100 + Y) * (121 + Y) : ℝ) := by positivity
  have hs : (0 : ℝ) < 277200000000000000000000 := by norm_num
  have hm : 0 < (277200000000000000000000) * pair2 Y := (mul_pos_iff_of_pos_right hd).mp hp
  exact (mul_pos_iff_of_pos_left hs).mp hm

#print axioms pair2_pos

noncomputable def kappa3 (x : ℝ) : ℝ :=
  (1) +
    ((-999959140973 / 1000000000000 : ℝ)) * x +
    ((998687184651 / 1000000000000 : ℝ)) * x ^ 2 +
    ((-985023741291 / 1000000000000 : ℝ)) * x ^ 3 +
    ((228310039519 / 250000000000 : ℝ)) * x ^ 4 +
    ((-702460268613 / 1000000000000 : ℝ)) * x ^ 5 +
    ((342182468893 / 1000000000000 : ℝ)) * x ^ 6 +
    ((-4102513387 / 31250000000 : ℝ)) * x ^ 8 +
    ((82013165569 / 1000000000000 : ℝ)) * x ^ 9 +
    ((-1739634547 / 100000000000 : ℝ)) * x ^ 10

noncomputable def coefficient3 (m : ℕ) : ℝ :=
  match m with
  | 0 => 1
  | 1 => (-999959140973 / 1000000000000 : ℝ)
  | 2 => (998687184651 / 1000000000000 : ℝ)
  | 3 => (-985023741291 / 1000000000000 : ℝ)
  | 4 => (228310039519 / 250000000000 : ℝ)
  | 5 => (-702460268613 / 1000000000000 : ℝ)
  | 6 => (342182468893 / 1000000000000 : ℝ)
  | 7 => 0
  | 8 => (-4102513387 / 31250000000 : ℝ)
  | 9 => (82013165569 / 1000000000000 : ℝ)
  | 10 => (-1739634547 / 100000000000 : ℝ)
  | _ => 0

lemma kappa3_sum (x : ℝ) :
    kappa3 x = ∑ m ∈ Finset.range 11, coefficient3 m * x ^ m := by
  norm_num [kappa3, coefficient3, Finset.sum_range_succ] 

lemma horizontal3_pos :
    0 < ∑ m ∈ Finset.range 11, (2 * m + 1 : ℝ) * coefficient3 m := by
  norm_num [coefficient3, Finset.sum_range_succ]

noncomputable def kappa3Derivative (x : ℝ) : ℝ :=
  ((-999959140973 / 1000000000000 : ℝ)) +
    ((998687184651 / 500000000000 : ℝ)) * x +
    ((-2955071223873 / 1000000000000 : ℝ)) * x ^ 2 +
    ((228310039519 / 62500000000 : ℝ)) * x ^ 3 +
    ((-702460268613 / 200000000000 : ℝ)) * x ^ 4 +
    ((1026547406679 / 500000000000 : ℝ)) * x ^ 5 +
    ((-4102513387 / 3906250000 : ℝ)) * x ^ 7 +
    ((738118490121 / 1000000000000 : ℝ)) * x ^ 8 +
    ((-1739634547 / 10000000000 : ℝ)) * x ^ 9

lemma kappa3_zero : kappa3 0 = 1 := by norm_num [kappa3]
lemma kappa3_pos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < kappa3 x := by
  unfold kappa3
  bernstein_bound (trust := kernel)
lemma kappa3_deriv_neg : ∀ x ∈ Set.Icc (0 : ℝ) 1, kappa3Derivative x < 0 := by
  unfold kappa3Derivative
  bernstein_bound (trust := kernel)
lemma kappa3_hasDerivAt (x : ℝ) : HasDerivAt kappa3 (kappa3Derivative x) x := by
  unfold kappa3 kappa3Derivative
  convert ((((((((((hasDerivAt_const x (1)).add (((hasDerivAt_id x).pow 1).const_mul ((-999959140973 / 1000000000000 : ℝ)))).add (((hasDerivAt_id x).pow 2).const_mul ((998687184651 / 1000000000000 : ℝ)))).add (((hasDerivAt_id x).pow 3).const_mul ((-985023741291 / 1000000000000 : ℝ)))).add (((hasDerivAt_id x).pow 4).const_mul ((228310039519 / 250000000000 : ℝ)))).add (((hasDerivAt_id x).pow 5).const_mul ((-702460268613 / 1000000000000 : ℝ)))).add (((hasDerivAt_id x).pow 6).const_mul ((342182468893 / 1000000000000 : ℝ)))).add (((hasDerivAt_id x).pow 8).const_mul ((-4102513387 / 31250000000 : ℝ)))).add (((hasDerivAt_id x).pow 9).const_mul ((82013165569 / 1000000000000 : ℝ)))).add (((hasDerivAt_id x).pow 10).const_mul ((-1739634547 / 100000000000 : ℝ)))) using 1 <;> (try funext y) <;> dsimp <;> ring
lemma kappa3_strictAnti : StrictAntiOn kappa3 (Set.Icc (0 : ℝ) 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc 0 1)
    (fun x _ => (kappa3_hasDerivAt x).continuousAt.continuousWithinAt)
  intro x hx
  rw [(kappa3_hasDerivAt x).deriv]
  exact kappa3_deriv_neg x (interior_subset hx)

noncomputable def pair3 (Y : ℝ) : ℝ :=
  ((4085456805438349 / 100000000000000000000 : ℝ)) / (1 + Y) +
    ((-254398204829670993 / 100000000000000000000 : ℝ)) / (4 + Y) +
    ((25618645655922109 / 625000000000000000 : ℝ)) / (9 + Y) +
    ((-22970903303648725059 / 80000000000000000000 : ℝ)) / (16 + Y) +
    ((526947423416566290281 / 500000000000000000000 : ℝ)) / (25 + Y) +
    ((-32425100267590708609 / 15000000000000000000 : ℝ)) / (36 + Y) +
    ((239527194762630995813 / 100000000000000000000 : ℝ)) / (49 + Y) +
    ((-26256130447528592331 / 25000000000000000000 : ℝ)) / (64 + Y) +
    ((-79813073291027820019 / 180000000000000000000 : ℝ)) / (81 + Y) +
    ((646167495826642259613 / 1000000000000000000000 : ℝ)) / (100 + Y) +
    ((-21049597003331811411 / 110000000000000000000 : ℝ)) / (121 + Y)

lemma pair3_from_coefficients (Y : ℝ) :
    pair3 Y = ∑ m ∈ Finset.range 11,
      (((m + 1 : ℝ) * (coefficient3 (m + 1) + coefficient3 m) -
        pairedEps ⟨2, by decide⟩ * |coefficient3 (m + 1) + coefficient3 m| / (m + 1)) /
          ((m + 1 : ℝ) ^ 2 + Y)) := by
  norm_num [pair3, coefficient3, pairedEps, Finset.sum_range_succ] 

noncomputable def numerator3 (Y : ℝ) : ℝ :=
  (103350815395058919645809909821440) +
    (-452409340247325652878434101020480) * Y +
    (653630133497770475777846666931248) * Y ^ 2 +
    (-179938056000729287269961731772972) * Y ^ 3 +
    (16364640163136953206099830849501) * Y ^ 4 +
    (-374176046533791230504889547334) * Y ^ 5 +
    (-748429926972722981164883221) * Y ^ 6 +
    (76948892325849005240333104) * Y ^ 7 +
    (-328516535720176176278653) * Y ^ 8 +
    (373686288104622603682) * Y ^ 9 +
    (7920014134315685) * Y ^ 10

noncomputable def compact3 (x : ℝ) : ℝ :=
  (103350815395058919645809909821440) +
    (-5557601556423845725242440108419200) * x +
    (110730640664814007720905181726932800) * x ^ 2 +
    (-878111623135389973285972530863916000) * x ^ 3 +
    (3655104684470947796672205824233014000) * x ^ 4 +
    (-9054404112235611182819187572311668480) * x ^ 5 +
    (14106017952264976953832288846792213200) * x ^ 6 +
    (-13993927521798232827327776634214984800) * x ^ 7 +
    (8598421872010037637025501773962394000) * x ^ 8 +
    (-2987819017163545595146232310178920000) * x ^ 9 +
    (449441375742232111477020901053533040) * x ^ 10

lemma compact3_pos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < compact3 x := by
  unfold compact3
  bernstein_bound 10 (trust := kernel)

lemma compact3_identity (Y : ℝ) (hY : 0 ≤ Y) :
    (Y + 10) ^ 10 * compact3 (Y / (Y + 10)) = 10 ^ 10 * numerator3 Y := by
  have h : Y + 10 ≠ 0 := by linarith
  unfold compact3 numerator3
  field_simp
  ring

lemma numerator3_pos (Y : ℝ) (hY : 0 ≤ Y) : 0 < numerator3 Y := by
  have hd : 0 < Y + 10 := by linarith
  have hx : Y / (Y + 10) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg hY hd.le
    · exact (div_le_one hd).mpr (by linarith)
  have hp := mul_pos (pow_pos hd 10) (compact3_pos _ hx)
  rw [compact3_identity Y hY] at hp
  exact (mul_pos_iff_of_pos_left (by norm_num : (0 : ℝ) < 10 ^ 10)).mp hp

lemma pair3_identity (Y : ℝ) (hY : 0 ≤ Y) :
    (39600000000000000000000) * pair3 Y * ((1 + Y) * (4 + Y) * (9 + Y) * (16 + Y) * (25 + Y) * (36 + Y) * (49 + Y) * (64 + Y) * (81 + Y) * (100 + Y) * (121 + Y)) = numerator3 Y := by
  have h1 : (1 : ℝ) + Y ≠ 0 := by linarith
  have h2 : (4 : ℝ) + Y ≠ 0 := by linarith
  have h3 : (9 : ℝ) + Y ≠ 0 := by linarith
  have h4 : (16 : ℝ) + Y ≠ 0 := by linarith
  have h5 : (25 : ℝ) + Y ≠ 0 := by linarith
  have h6 : (36 : ℝ) + Y ≠ 0 := by linarith
  have h7 : (49 : ℝ) + Y ≠ 0 := by linarith
  have h8 : (64 : ℝ) + Y ≠ 0 := by linarith
  have h9 : (81 : ℝ) + Y ≠ 0 := by linarith
  have h10 : (100 : ℝ) + Y ≠ 0 := by linarith
  have h11 : (121 : ℝ) + Y ≠ 0 := by linarith
  unfold pair3 numerator3
  field_simp
  ring

lemma pair3_pos (Y : ℝ) (hY : 0 ≤ Y) : 0 < pair3 Y := by
  have hp := numerator3_pos Y hY
  rw [← pair3_identity Y hY] at hp
  have hd : 0 < ((1 + Y) * (4 + Y) * (9 + Y) * (16 + Y) * (25 + Y) * (36 + Y) * (49 + Y) * (64 + Y) * (81 + Y) * (100 + Y) * (121 + Y) : ℝ) := by positivity
  have hs : (0 : ℝ) < 39600000000000000000000 := by norm_num
  have hm : 0 < (39600000000000000000000) * pair3 Y := (mul_pos_iff_of_pos_right hd).mp hp
  exact (mul_pos_iff_of_pos_left hs).mp hm

#print axioms pair3_pos

noncomputable def kappa4 (x : ℝ) : ℝ :=
  (1) +
    ((-499988889997 / 500000000000 : ℝ)) * x +
    ((999234426187 / 1000000000000 : ℝ)) * x ^ 2 +
    ((-247675991013 / 250000000000 : ℝ)) * x ^ 3 +
    ((471388924643 / 500000000000 : ℝ)) * x ^ 4 +
    ((-197757168157 / 250000000000 : ℝ)) * x ^ 5 +
    ((505196913937 / 1000000000000 : ℝ)) * x ^ 6 +
    ((-187383296683 / 1000000000000 : ℝ)) * x ^ 7 +
    ((30702914887 / 1000000000000 : ℝ)) * x ^ 9 +
    ((-2204148053 / 250000000000 : ℝ)) * x ^ 10

noncomputable def coefficient4 (m : ℕ) : ℝ :=
  match m with
  | 0 => 1
  | 1 => (-499988889997 / 500000000000 : ℝ)
  | 2 => (999234426187 / 1000000000000 : ℝ)
  | 3 => (-247675991013 / 250000000000 : ℝ)
  | 4 => (471388924643 / 500000000000 : ℝ)
  | 5 => (-197757168157 / 250000000000 : ℝ)
  | 6 => (505196913937 / 1000000000000 : ℝ)
  | 7 => (-187383296683 / 1000000000000 : ℝ)
  | 8 => 0
  | 9 => (30702914887 / 1000000000000 : ℝ)
  | 10 => (-2204148053 / 250000000000 : ℝ)
  | _ => 0

lemma kappa4_sum (x : ℝ) :
    kappa4 x = ∑ m ∈ Finset.range 11, coefficient4 m * x ^ m := by
  norm_num [kappa4, coefficient4, Finset.sum_range_succ] 

lemma horizontal4_pos :
    0 < ∑ m ∈ Finset.range 11, (2 * m + 1 : ℝ) * coefficient4 m := by
  norm_num [coefficient4, Finset.sum_range_succ]

noncomputable def kappa4Derivative (x : ℝ) : ℝ :=
  ((-499988889997 / 500000000000 : ℝ)) +
    ((999234426187 / 500000000000 : ℝ)) * x +
    ((-743027973039 / 250000000000 : ℝ)) * x ^ 2 +
    ((471388924643 / 125000000000 : ℝ)) * x ^ 3 +
    ((-197757168157 / 50000000000 : ℝ)) * x ^ 4 +
    ((1515590741811 / 500000000000 : ℝ)) * x ^ 5 +
    ((-1311683076781 / 1000000000000 : ℝ)) * x ^ 6 +
    ((276326233983 / 1000000000000 : ℝ)) * x ^ 8 +
    ((-2204148053 / 25000000000 : ℝ)) * x ^ 9

lemma kappa4_zero : kappa4 0 = 1 := by norm_num [kappa4]
lemma kappa4_pos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < kappa4 x := by
  unfold kappa4
  bernstein_bound (trust := kernel)
lemma kappa4_deriv_neg : ∀ x ∈ Set.Icc (0 : ℝ) 1, kappa4Derivative x < 0 := by
  unfold kappa4Derivative
  bernstein_bound (trust := kernel)
lemma kappa4_hasDerivAt (x : ℝ) : HasDerivAt kappa4 (kappa4Derivative x) x := by
  unfold kappa4 kappa4Derivative
  convert ((((((((((hasDerivAt_const x (1)).add (((hasDerivAt_id x).pow 1).const_mul ((-499988889997 / 500000000000 : ℝ)))).add (((hasDerivAt_id x).pow 2).const_mul ((999234426187 / 1000000000000 : ℝ)))).add (((hasDerivAt_id x).pow 3).const_mul ((-247675991013 / 250000000000 : ℝ)))).add (((hasDerivAt_id x).pow 4).const_mul ((471388924643 / 500000000000 : ℝ)))).add (((hasDerivAt_id x).pow 5).const_mul ((-197757168157 / 250000000000 : ℝ)))).add (((hasDerivAt_id x).pow 6).const_mul ((505196913937 / 1000000000000 : ℝ)))).add (((hasDerivAt_id x).pow 7).const_mul ((-187383296683 / 1000000000000 : ℝ)))).add (((hasDerivAt_id x).pow 9).const_mul ((30702914887 / 1000000000000 : ℝ)))).add (((hasDerivAt_id x).pow 10).const_mul ((-2204148053 / 250000000000 : ℝ)))) using 1 <;> (try funext y) <;> dsimp <;> ring
lemma kappa4_strictAnti : StrictAntiOn kappa4 (Set.Icc (0 : ℝ) 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc 0 1)
    (fun x _ => (kappa4_hasDerivAt x).continuousAt.continuousWithinAt)
  intro x hx
  rw [(kappa4_hasDerivAt x).deriv]
  exact kappa4_deriv_neg x (interior_subset hx)

noncomputable def pair4 (Y : ℝ) : ℝ :=
  ((555455743318009 / 25000000000000000000 : ℝ)) / (1 + Y) +
    ((-148673732585166579 / 100000000000000000000 : ℝ)) / (4 + Y) +
    ((767734772898569281 / 30000000000000000000 : ℝ)) / (9 + Y) +
    ((-19170541686740359851 / 100000000000000000000 : ℝ)) / (16 + Y) +
    ((94842932140520448987 / 125000000000000000000 : ℝ)) / (25 + Y) +
    ((-171499436037779829309 / 100000000000000000000 : ℝ)) / (36 + Y) +
    ((55617292283662273983 / 25000000000000000000 : ℝ)) / (49 + Y) +
    ((-599627298356636841951 / 400000000000000000000 : ℝ)) / (64 + Y) +
    ((124346682572799196661 / 450000000000000000000 : ℝ)) / (81 + Y) +
    ((4377261035814730721 / 20000000000000000000 : ℝ)) / (100 + Y) +
    ((-13335104530629767841 / 137500000000000000000 : ℝ)) / (121 + Y)

lemma pair4_from_coefficients (Y : ℝ) :
    pair4 Y = ∑ m ∈ Finset.range 11,
      (((m + 1 : ℝ) * (coefficient4 (m + 1) + coefficient4 m) -
        pairedEps ⟨3, by decide⟩ * |coefficient4 (m + 1) + coefficient4 m| / (m + 1)) /
          ((m + 1 : ℝ) ^ 2 + Y)) := by
  norm_num [pair4, coefficient4, pairedEps, Finset.sum_range_succ] 

noncomputable def numerator4 (Y : ℝ) : ℝ :=
  (282879587302765305500060874316800) +
    (-1150423973608795940026656576839232) * Y +
    (1801705523990897629204546860579088) * Y ^ 2 +
    (-533215918065001042000184569086892) * Y ^ 3 +
    (53590289024787469115503016910103) * Y ^ 4 +
    (-1534234085952930241544682556882) * Y ^ 5 +
    (5875528780909638453095612713) * Y ^ 6 +
    (222021494135612599253523368) * Y ^ 7 +
    (-1384957723844128528874087) * Y ^ 8 +
    (2150580386236813179638) * Y ^ 9 +
    (39598694010875383) * Y ^ 10

noncomputable def compact4 (x : ℝ) : ℝ :=
  (282879587302765305500060874316800) +
    (-14333035609115612455267174511560320) * x +
    (296438291452505836270356517317695680) * x ^ 2 +
    (-2422678518233217520433425730130301920) * x ^ 3 +
    (10338950635042364650706457670482203280) * x ^ 4 +
    (-26176745826543969518053590267507270720) * x ^ 5 +
    (41594970645767478599577777440188246320) * x ^ 6 +
    (-42025983546024490112299454322821683680) * x ^ 7 +
    (26270423430227381869691921927388007920) * x ^ 8 +
    (-9279339511783673066040673760189393280) * x ^ 9 +
    (1418014556513419047839151468909739920) * x ^ 10

lemma compact4_pos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < compact4 x := by
  unfold compact4
  bernstein_bound 10 (trust := kernel)

lemma compact4_identity (Y : ℝ) (hY : 0 ≤ Y) :
    (Y + 10) ^ 10 * compact4 (Y / (Y + 10)) = 10 ^ 10 * numerator4 Y := by
  have h : Y + 10 ≠ 0 := by linarith
  unfold compact4 numerator4
  field_simp
  ring

lemma numerator4_pos (Y : ℝ) (hY : 0 ≤ Y) : 0 < numerator4 Y := by
  have hd : 0 < Y + 10 := by linarith
  have hx : Y / (Y + 10) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg hY hd.le
    · exact (div_le_one hd).mpr (by linarith)
  have hp := mul_pos (pow_pos hd 10) (compact4_pos _ hx)
  rw [compact4_identity Y hY] at hp
  exact (mul_pos_iff_of_pos_left (by norm_num : (0 : ℝ) < 10 ^ 10)).mp hp

lemma pair4_identity (Y : ℝ) (hY : 0 ≤ Y) :
    (198000000000000000000000) * pair4 Y * ((1 + Y) * (4 + Y) * (9 + Y) * (16 + Y) * (25 + Y) * (36 + Y) * (49 + Y) * (64 + Y) * (81 + Y) * (100 + Y) * (121 + Y)) = numerator4 Y := by
  have h1 : (1 : ℝ) + Y ≠ 0 := by linarith
  have h2 : (4 : ℝ) + Y ≠ 0 := by linarith
  have h3 : (9 : ℝ) + Y ≠ 0 := by linarith
  have h4 : (16 : ℝ) + Y ≠ 0 := by linarith
  have h5 : (25 : ℝ) + Y ≠ 0 := by linarith
  have h6 : (36 : ℝ) + Y ≠ 0 := by linarith
  have h7 : (49 : ℝ) + Y ≠ 0 := by linarith
  have h8 : (64 : ℝ) + Y ≠ 0 := by linarith
  have h9 : (81 : ℝ) + Y ≠ 0 := by linarith
  have h10 : (100 : ℝ) + Y ≠ 0 := by linarith
  have h11 : (121 : ℝ) + Y ≠ 0 := by linarith
  unfold pair4 numerator4
  field_simp
  ring

lemma pair4_pos (Y : ℝ) (hY : 0 ≤ Y) : 0 < pair4 Y := by
  have hp := numerator4_pos Y hY
  rw [← pair4_identity Y hY] at hp
  have hd : 0 < ((1 + Y) * (4 + Y) * (9 + Y) * (16 + Y) * (25 + Y) * (36 + Y) * (49 + Y) * (64 + Y) * (81 + Y) * (100 + Y) * (121 + Y) : ℝ) := by positivity
  have hs : (0 : ℝ) < 198000000000000000000000 := by norm_num
  have hm : 0 < (198000000000000000000000) * pair4 Y := (mul_pos_iff_of_pos_right hd).mp hp
  exact (mul_pos_iff_of_pos_left hs).mp hm

#print axioms pair4_pos

noncomputable def kappa5 (x : ℝ) : ℝ :=
  (1) +
    ((-999981121591 / 1000000000000 : ℝ)) * x +
    ((499662519843 / 500000000000 : ℝ)) * x ^ 2 +
    ((-991531939227 / 1000000000000 : ℝ)) * x ^ 3 +
    ((94640583039 / 100000000000 : ℝ)) * x ^ 4 +
    ((-399813125131 / 500000000000 : ℝ)) * x ^ 5 +
    ((516325105649 / 1000000000000 : ℝ)) * x ^ 6 +
    ((-38827672481 / 200000000000 : ℝ)) * x ^ 7 +
    ((32774736667 / 1000000000000 : ℝ)) * x ^ 9 +
    ((-9551506543 / 1000000000000 : ℝ)) * x ^ 10

noncomputable def coefficient5 (m : ℕ) : ℝ :=
  match m with
  | 0 => 1
  | 1 => (-999981121591 / 1000000000000 : ℝ)
  | 2 => (499662519843 / 500000000000 : ℝ)
  | 3 => (-991531939227 / 1000000000000 : ℝ)
  | 4 => (94640583039 / 100000000000 : ℝ)
  | 5 => (-399813125131 / 500000000000 : ℝ)
  | 6 => (516325105649 / 1000000000000 : ℝ)
  | 7 => (-38827672481 / 200000000000 : ℝ)
  | 8 => 0
  | 9 => (32774736667 / 1000000000000 : ℝ)
  | 10 => (-9551506543 / 1000000000000 : ℝ)
  | _ => 0

lemma kappa5_sum (x : ℝ) :
    kappa5 x = ∑ m ∈ Finset.range 11, coefficient5 m * x ^ m := by
  norm_num [kappa5, coefficient5, Finset.sum_range_succ] 

lemma horizontal5_pos :
    0 < ∑ m ∈ Finset.range 11, (2 * m + 1 : ℝ) * coefficient5 m := by
  norm_num [coefficient5, Finset.sum_range_succ]

noncomputable def kappa5Derivative (x : ℝ) : ℝ :=
  ((-999981121591 / 1000000000000 : ℝ)) +
    ((499662519843 / 250000000000 : ℝ)) * x +
    ((-2974595817681 / 1000000000000 : ℝ)) * x ^ 2 +
    ((94640583039 / 25000000000 : ℝ)) * x ^ 3 +
    ((-399813125131 / 100000000000 : ℝ)) * x ^ 4 +
    ((1548975316947 / 500000000000 : ℝ)) * x ^ 5 +
    ((-271793707367 / 200000000000 : ℝ)) * x ^ 6 +
    ((294972630003 / 1000000000000 : ℝ)) * x ^ 8 +
    ((-9551506543 / 100000000000 : ℝ)) * x ^ 9

lemma kappa5_zero : kappa5 0 = 1 := by norm_num [kappa5]
lemma kappa5_pos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < kappa5 x := by
  unfold kappa5
  bernstein_bound (trust := kernel)
lemma kappa5_deriv_neg : ∀ x ∈ Set.Icc (0 : ℝ) 1, kappa5Derivative x < 0 := by
  unfold kappa5Derivative
  bernstein_bound (trust := kernel)
lemma kappa5_hasDerivAt (x : ℝ) : HasDerivAt kappa5 (kappa5Derivative x) x := by
  unfold kappa5 kappa5Derivative
  convert ((((((((((hasDerivAt_const x (1)).add (((hasDerivAt_id x).pow 1).const_mul ((-999981121591 / 1000000000000 : ℝ)))).add (((hasDerivAt_id x).pow 2).const_mul ((499662519843 / 500000000000 : ℝ)))).add (((hasDerivAt_id x).pow 3).const_mul ((-991531939227 / 1000000000000 : ℝ)))).add (((hasDerivAt_id x).pow 4).const_mul ((94640583039 / 100000000000 : ℝ)))).add (((hasDerivAt_id x).pow 5).const_mul ((-399813125131 / 500000000000 : ℝ)))).add (((hasDerivAt_id x).pow 6).const_mul ((516325105649 / 1000000000000 : ℝ)))).add (((hasDerivAt_id x).pow 7).const_mul ((-38827672481 / 200000000000 : ℝ)))).add (((hasDerivAt_id x).pow 9).const_mul ((32774736667 / 1000000000000 : ℝ)))).add (((hasDerivAt_id x).pow 10).const_mul ((-9551506543 / 1000000000000 : ℝ)))) using 1 <;> (try funext y) <;> dsimp <;> ring
lemma kappa5_strictAnti : StrictAntiOn kappa5 (Set.Icc (0 : ℝ) 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc 0 1)
    (fun x _ => (kappa5_hasDerivAt x).continuousAt.continuousWithinAt)
  intro x hx
  rw [(kappa5_hasDerivAt x).deriv]
  exact kappa5_deriv_neg x (interior_subset hx)

noncomputable def pair5 (Y : ℝ) : ℝ :=
  ((471929094503559 / 25000000000000000000 : ℝ)) / (1 + Y) +
    ((-13121854475812269 / 10000000000000000000 : ℝ)) / (4 + Y) +
    ((584478250817447703 / 25000000000000000000 : ℝ)) / (9 + Y) +
    ((-18050517947753472213 / 100000000000000000000 : ℝ)) / (16 + Y) +
    ((2866781110639761529 / 3906250000000000000 : ℝ)) / (25 + Y) +
    ((-84990499105095822279 / 50000000000000000000 : ℝ)) / (36 + Y) +
    ((98669557296990097661 / 43750000000000000000 : ℝ)) / (49 + Y) +
    ((-62124339996431921169 / 40000000000000000000 : ℝ)) / (64 + Y) +
    ((66368787705134236117 / 225000000000000000000 : ℝ)) / (81 + Y) +
    ((14514509253723381381 / 62500000000000000000 : ℝ)) / (100 + Y) +
    ((-28893323043009289407 / 275000000000000000000 : ℝ)) / (121 + Y)

lemma pair5_from_coefficients (Y : ℝ) :
    pair5 Y = ∑ m ∈ Finset.range 11,
      (((m + 1 : ℝ) * (coefficient5 (m + 1) + coefficient5 m) -
        pairedEps ⟨4, by decide⟩ * |coefficient5 (m + 1) + coefficient5 m| / (m + 1)) /
          ((m + 1 : ℝ) ^ 2 + Y)) := by
  norm_num [pair5, coefficient5, pairedEps, Finset.sum_range_succ] 

noncomputable def numerator5 (Y : ℝ) : ℝ :=
  (168905009660185823047911042554880) +
    (-663809227531401767271121229750208) * Y +
    (1073279690836239322133840104181296) * Y ^ 2 +
    (-331624077941815876673587297755028) * Y ^ 3 +
    (35170939227353023184415618761941) * Y ^ 4 +
    (-1098059967212245033933261818598) * Y ^ 5 +
    (5891623157911347572455873771) * Y ^ 6 +
    (153967175202776184653474312) * Y ^ 7 +
    (-1149706896228279978183749) * Y ^ 8 +
    (2063142226197778445522) * Y ^ 9 +
    (27717731931247861) * Y ^ 10

noncomputable def compact5 (x : ℝ) : ℝ :=
  (168905009660185823047911042554880) +
    (-8327142371915875903190322723050880) * x +
    (174671524996158453304940918010617920) * x ^ 2 +
    (-1449487753681334269364012348916725280) * x ^ 3 +
    (6271330875362727977881822715538934320) * x ^ 4 +
    (-16073497944947412562722787476056197440) * x ^ 5 +
    (25822232733402423530315539816477988880) * x ^ 6 +
    (-26349351982494562970058225485888197920) * x ^ 7 +
    (16620177422782576993867762455443411280) * x ^ 8 +
    (-5919425988937524770714768217672760320) * x ^ 9 +
    (911509351156380626882348644743424560) * x ^ 10

lemma compact5_pos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < compact5 x := by
  unfold compact5
  bernstein_bound 10 (trust := kernel)

lemma compact5_identity (Y : ℝ) (hY : 0 ≤ Y) :
    (Y + 10) ^ 10 * compact5 (Y / (Y + 10)) = 10 ^ 10 * numerator5 Y := by
  have h : Y + 10 ≠ 0 := by linarith
  unfold compact5 numerator5
  field_simp
  ring

lemma numerator5_pos (Y : ℝ) (hY : 0 ≤ Y) : 0 < numerator5 Y := by
  have hd : 0 < Y + 10 := by linarith
  have hx : Y / (Y + 10) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg hY hd.le
    · exact (div_le_one hd).mpr (by linarith)
  have hp := mul_pos (pow_pos hd 10) (compact5_pos _ hx)
  rw [compact5_identity Y hY] at hp
  exact (mul_pos_iff_of_pos_left (by norm_num : (0 : ℝ) < 10 ^ 10)).mp hp

lemma pair5_identity (Y : ℝ) (hY : 0 ≤ Y) :
    (138600000000000000000000) * pair5 Y * ((1 + Y) * (4 + Y) * (9 + Y) * (16 + Y) * (25 + Y) * (36 + Y) * (49 + Y) * (64 + Y) * (81 + Y) * (100 + Y) * (121 + Y)) = numerator5 Y := by
  have h1 : (1 : ℝ) + Y ≠ 0 := by linarith
  have h2 : (4 : ℝ) + Y ≠ 0 := by linarith
  have h3 : (9 : ℝ) + Y ≠ 0 := by linarith
  have h4 : (16 : ℝ) + Y ≠ 0 := by linarith
  have h5 : (25 : ℝ) + Y ≠ 0 := by linarith
  have h6 : (36 : ℝ) + Y ≠ 0 := by linarith
  have h7 : (49 : ℝ) + Y ≠ 0 := by linarith
  have h8 : (64 : ℝ) + Y ≠ 0 := by linarith
  have h9 : (81 : ℝ) + Y ≠ 0 := by linarith
  have h10 : (100 : ℝ) + Y ≠ 0 := by linarith
  have h11 : (121 : ℝ) + Y ≠ 0 := by linarith
  unfold pair5 numerator5
  field_simp
  ring

lemma pair5_pos (Y : ℝ) (hY : 0 ≤ Y) : 0 < pair5 Y := by
  have hp := numerator5_pos Y hY
  rw [← pair5_identity Y hY] at hp
  have hd : 0 < ((1 + Y) * (4 + Y) * (9 + Y) * (16 + Y) * (25 + Y) * (36 + Y) * (49 + Y) * (64 + Y) * (81 + Y) * (100 + Y) * (121 + Y) : ℝ) := by positivity
  have hs : (0 : ℝ) < 138600000000000000000000 := by norm_num
  have hm : 0 < (138600000000000000000000) * pair5 Y := (mul_pos_iff_of_pos_right hd).mp hp
  exact (mul_pos_iff_of_pos_left hs).mp hm

#print axioms pair5_pos

noncomputable def kappa6 (x : ℝ) : ℝ :=
  (1) +
    ((-999981868859 / 1000000000000 : ℝ)) * x +
    ((499673831987 / 500000000000 : ℝ)) * x ^ 2 +
    ((-991748468269 / 1000000000000 : ℝ)) * x ^ 3 +
    ((947379889067 / 1000000000000 : ℝ)) * x ^ 4 +
    ((-32078899463 / 40000000000 : ℝ)) * x ^ 5 +
    ((259697039929 / 500000000000 : ℝ)) * x ^ 6 +
    ((-196014531499 / 1000000000000 : ℝ)) * x ^ 7 +
    ((6671029233 / 200000000000 : ℝ)) * x ^ 9 +
    ((-304936727 / 31250000000 : ℝ)) * x ^ 10

noncomputable def coefficient6 (m : ℕ) : ℝ :=
  match m with
  | 0 => 1
  | 1 => (-999981868859 / 1000000000000 : ℝ)
  | 2 => (499673831987 / 500000000000 : ℝ)
  | 3 => (-991748468269 / 1000000000000 : ℝ)
  | 4 => (947379889067 / 1000000000000 : ℝ)
  | 5 => (-32078899463 / 40000000000 : ℝ)
  | 6 => (259697039929 / 500000000000 : ℝ)
  | 7 => (-196014531499 / 1000000000000 : ℝ)
  | 8 => 0
  | 9 => (6671029233 / 200000000000 : ℝ)
  | 10 => (-304936727 / 31250000000 : ℝ)
  | _ => 0

lemma kappa6_sum (x : ℝ) :
    kappa6 x = ∑ m ∈ Finset.range 11, coefficient6 m * x ^ m := by
  norm_num [kappa6, coefficient6, Finset.sum_range_succ] 

lemma horizontal6_pos :
    0 < ∑ m ∈ Finset.range 11, (2 * m + 1 : ℝ) * coefficient6 m := by
  norm_num [coefficient6, Finset.sum_range_succ]

noncomputable def kappa6Derivative (x : ℝ) : ℝ :=
  ((-999981868859 / 1000000000000 : ℝ)) +
    ((499673831987 / 250000000000 : ℝ)) * x +
    ((-2975245404807 / 1000000000000 : ℝ)) * x ^ 2 +
    ((947379889067 / 250000000000 : ℝ)) * x ^ 3 +
    ((-32078899463 / 8000000000 : ℝ)) * x ^ 4 +
    ((779091119787 / 250000000000 : ℝ)) * x ^ 5 +
    ((-1372101720493 / 1000000000000 : ℝ)) * x ^ 6 +
    ((60039263097 / 200000000000 : ℝ)) * x ^ 8 +
    ((-304936727 / 3125000000 : ℝ)) * x ^ 9

lemma kappa6_zero : kappa6 0 = 1 := by norm_num [kappa6]
lemma kappa6_pos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < kappa6 x := by
  unfold kappa6
  bernstein_bound (trust := kernel)
lemma kappa6_deriv_neg : ∀ x ∈ Set.Icc (0 : ℝ) 1, kappa6Derivative x < 0 := by
  unfold kappa6Derivative
  bernstein_bound (trust := kernel)
lemma kappa6_hasDerivAt (x : ℝ) : HasDerivAt kappa6 (kappa6Derivative x) x := by
  unfold kappa6 kappa6Derivative
  convert ((((((((((hasDerivAt_const x (1)).add (((hasDerivAt_id x).pow 1).const_mul ((-999981868859 / 1000000000000 : ℝ)))).add (((hasDerivAt_id x).pow 2).const_mul ((499673831987 / 500000000000 : ℝ)))).add (((hasDerivAt_id x).pow 3).const_mul ((-991748468269 / 1000000000000 : ℝ)))).add (((hasDerivAt_id x).pow 4).const_mul ((947379889067 / 1000000000000 : ℝ)))).add (((hasDerivAt_id x).pow 5).const_mul ((-32078899463 / 40000000000 : ℝ)))).add (((hasDerivAt_id x).pow 6).const_mul ((259697039929 / 500000000000 : ℝ)))).add (((hasDerivAt_id x).pow 7).const_mul ((-196014531499 / 1000000000000 : ℝ)))).add (((hasDerivAt_id x).pow 9).const_mul ((6671029233 / 200000000000 : ℝ)))).add (((hasDerivAt_id x).pow 10).const_mul ((-304936727 / 31250000000 : ℝ)))) using 1 <;> (try funext y) <;> dsimp <;> ring
lemma kappa6_strictAnti : StrictAntiOn kappa6 (Set.Icc (0 : ℝ) 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc 0 1)
    (fun x _ => (kappa6_hasDerivAt x).continuousAt.continuousWithinAt)
  intro x hx
  rw [(kappa6_hasDerivAt x).deriv]
  exact kappa6_deriv_neg x (interior_subset hx)

noncomputable def pair6 (Y : ℝ) : ℝ :=
  ((1813003373121913 / 100000000000000000000 : ℝ)) / (1 + Y) +
    ((-50737165417846539 / 40000000000000000000 : ℝ)) / (4 + Y) +
    ((455948648414121971 / 20000000000000000000 : ℝ)) / (9 + Y) +
    ((-35494998841056593307 / 200000000000000000000 : ℝ)) / (16 + Y) +
    ((90879404556748245339 / 125000000000000000000 : ℝ)) / (25 + Y) +
    ((-339094663295843273573 / 200000000000000000000 : ℝ)) / (36 + Y) +
    ((226365401725742595941 / 100000000000000000000 : ℝ)) / (49 + Y) +
    ((-1254494198654343864393 / 800000000000000000000 : ℝ)) / (64 + Y) +
    ((18011765349108158023 / 60000000000000000000 : ℝ)) / (81 + Y) +
    ((235971564902077307593 / 1000000000000000000000 : ℝ)) / (100 + Y) +
    ((-3689736258948591789 / 34375000000000000000 : ℝ)) / (121 + Y)

lemma pair6_from_coefficients (Y : ℝ) :
    pair6 Y = ∑ m ∈ Finset.range 11,
      (((m + 1 : ℝ) * (coefficient6 (m + 1) + coefficient6 m) -
        pairedEps ⟨5, by decide⟩ * |coefficient6 (m + 1) + coefficient6 m| / (m + 1)) /
          ((m + 1 : ℝ) ^ 2 + Y)) := by
  norm_num [pair6, coefficient6, pairedEps, Finset.sum_range_succ] 

noncomputable def numerator6 (Y : ℝ) : ℝ :=
  (31302055945787086466114565749760) +
    (-121072177990192497745702285136448) * Y +
    (195743812542628027281710147195792) * Y ^ 2 +
    (-61079962902976990813847599258028) * Y ^ 3 +
    (6570588809729171596820793198527) * Y ^ 4 +
    (-210297304755619281424985999138) * Y ^ 5 +
    (1219902840312621046198209857) * Y ^ 6 +
    (29261328448799351468922952) * Y ^ 7 +
    (-228480847489398101544463) * Y ^ 8 +
    (423964261566930218662) * Y ^ 9 +
    (5280088423218527) * Y ^ 10

noncomputable def compact6 (x : ℝ) : ℝ :=
  (31302055945787086466114565749760) +
    (-1523742339359795842118168508862080) * x +
    (31879469790940546416259375840598720) * x ^ 2 +
    (-265017243727043162203602287553754080) * x ^ 3 +
    (1149622364797866114318203517261749520) * x ^ 4 +
    (-2954548692626526876769168350381307200) * x ^ 5 +
    (4759086642096346706055916131685948080) * x ^ 6 +
    (-4868422992846383871203814714483402720) * x ^ 7 +
    (3078060827994562828430088077873716080) * x ^ 8 +
    (-1098703939269103546796013851631227520) * x ^ 9 +
    (169536004125556154739969425330791440) * x ^ 10

lemma compact6_pos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < compact6 x := by
  unfold compact6
  bernstein_bound 10 (trust := kernel)

lemma compact6_identity (Y : ℝ) (hY : 0 ≤ Y) :
    (Y + 10) ^ 10 * compact6 (Y / (Y + 10)) = 10 ^ 10 * numerator6 Y := by
  have h : Y + 10 ≠ 0 := by linarith
  unfold compact6 numerator6
  field_simp
  ring

lemma numerator6_pos (Y : ℝ) (hY : 0 ≤ Y) : 0 < numerator6 Y := by
  have hd : 0 < Y + 10 := by linarith
  have hx : Y / (Y + 10) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg hY hd.le
    · exact (div_le_one hd).mpr (by linarith)
  have hp := mul_pos (pow_pos hd 10) (compact6_pos _ hx)
  rw [compact6_identity Y hY] at hp
  exact (mul_pos_iff_of_pos_left (by norm_num : (0 : ℝ) < 10 ^ 10)).mp hp

lemma pair6_identity (Y : ℝ) (hY : 0 ≤ Y) :
    (26400000000000000000000) * pair6 Y * ((1 + Y) * (4 + Y) * (9 + Y) * (16 + Y) * (25 + Y) * (36 + Y) * (49 + Y) * (64 + Y) * (81 + Y) * (100 + Y) * (121 + Y)) = numerator6 Y := by
  have h1 : (1 : ℝ) + Y ≠ 0 := by linarith
  have h2 : (4 : ℝ) + Y ≠ 0 := by linarith
  have h3 : (9 : ℝ) + Y ≠ 0 := by linarith
  have h4 : (16 : ℝ) + Y ≠ 0 := by linarith
  have h5 : (25 : ℝ) + Y ≠ 0 := by linarith
  have h6 : (36 : ℝ) + Y ≠ 0 := by linarith
  have h7 : (49 : ℝ) + Y ≠ 0 := by linarith
  have h8 : (64 : ℝ) + Y ≠ 0 := by linarith
  have h9 : (81 : ℝ) + Y ≠ 0 := by linarith
  have h10 : (100 : ℝ) + Y ≠ 0 := by linarith
  have h11 : (121 : ℝ) + Y ≠ 0 := by linarith
  unfold pair6 numerator6
  field_simp
  ring

lemma pair6_pos (Y : ℝ) (hY : 0 ≤ Y) : 0 < pair6 Y := by
  have hp := numerator6_pos Y hY
  rw [← pair6_identity Y hY] at hp
  have hd : 0 < ((1 + Y) * (4 + Y) * (9 + Y) * (16 + Y) * (25 + Y) * (36 + Y) * (49 + Y) * (64 + Y) * (81 + Y) * (100 + Y) * (121 + Y) : ℝ) := by positivity
  have hs : (0 : ℝ) < 26400000000000000000000 := by norm_num
  have hm : 0 < (26400000000000000000000) * pair6 Y := (mul_pos_iff_of_pos_right hd).mp hp
  exact (mul_pos_iff_of_pos_left hs).mp hm

#print axioms pair6_pos

noncomputable def kappa7 (x : ℝ) : ℝ :=
  (1) +
    ((-999978588421 / 1000000000000 : ℝ)) * x +
    ((999193002543 / 1000000000000 : ℝ)) * x ^ 2 +
    ((-989319433553 / 1000000000000 : ℝ)) * x ^ 3 +
    ((929535157749 / 1000000000000 : ℝ)) * x ^ 4 +
    ((-18278482591 / 25000000000 : ℝ)) * x ^ 5 +
    ((71960568387 / 200000000000 : ℝ)) * x ^ 6 +
    ((-97801312287 / 1000000000000 : ℝ)) * x ^ 8 +
    ((9324153817 / 250000000000 : ℝ)) * x ^ 10 +
    ((-111714529 / 8000000000 : ℝ)) * x ^ 13 +
    ((6376973401 / 1000000000000 : ℝ)) * x ^ 14

noncomputable def coefficient7 (m : ℕ) : ℝ :=
  match m with
  | 0 => 1
  | 1 => (-999978588421 / 1000000000000 : ℝ)
  | 2 => (999193002543 / 1000000000000 : ℝ)
  | 3 => (-989319433553 / 1000000000000 : ℝ)
  | 4 => (929535157749 / 1000000000000 : ℝ)
  | 5 => (-18278482591 / 25000000000 : ℝ)
  | 6 => (71960568387 / 200000000000 : ℝ)
  | 7 => 0
  | 8 => (-97801312287 / 1000000000000 : ℝ)
  | 9 => 0
  | 10 => (9324153817 / 250000000000 : ℝ)
  | 11 => 0
  | 12 => 0
  | 13 => (-111714529 / 8000000000 : ℝ)
  | 14 => (6376973401 / 1000000000000 : ℝ)
  | _ => 0

lemma kappa7_sum (x : ℝ) :
    kappa7 x = ∑ m ∈ Finset.range 15, coefficient7 m * x ^ m := by
  norm_num [kappa7, coefficient7, Finset.sum_range_succ] 

lemma horizontal7_pos :
    0 < ∑ m ∈ Finset.range 15, (2 * m + 1 : ℝ) * coefficient7 m := by
  norm_num [coefficient7, Finset.sum_range_succ]

noncomputable def kappa7Derivative (x : ℝ) : ℝ :=
  ((-999978588421 / 1000000000000 : ℝ)) +
    ((999193002543 / 500000000000 : ℝ)) * x +
    ((-2967958300659 / 1000000000000 : ℝ)) * x ^ 2 +
    ((929535157749 / 250000000000 : ℝ)) * x ^ 3 +
    ((-18278482591 / 5000000000 : ℝ)) * x ^ 4 +
    ((215881705161 / 100000000000 : ℝ)) * x ^ 5 +
    ((-97801312287 / 125000000000 : ℝ)) * x ^ 7 +
    ((9324153817 / 25000000000 : ℝ)) * x ^ 9 +
    ((-1452288877 / 8000000000 : ℝ)) * x ^ 12 +
    ((44638813807 / 500000000000 : ℝ)) * x ^ 13

lemma kappa7_zero : kappa7 0 = 1 := by norm_num [kappa7]
lemma kappa7_pos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < kappa7 x := by
  unfold kappa7
  bernstein_bound (trust := kernel)
lemma kappa7_deriv_neg : ∀ x ∈ Set.Icc (0 : ℝ) 1, kappa7Derivative x < 0 := by
  unfold kappa7Derivative
  bernstein_bound (trust := kernel)
lemma kappa7_hasDerivAt (x : ℝ) : HasDerivAt kappa7 (kappa7Derivative x) x := by
  unfold kappa7 kappa7Derivative
  convert (((((((((((hasDerivAt_const x (1)).add (((hasDerivAt_id x).pow 1).const_mul ((-999978588421 / 1000000000000 : ℝ)))).add (((hasDerivAt_id x).pow 2).const_mul ((999193002543 / 1000000000000 : ℝ)))).add (((hasDerivAt_id x).pow 3).const_mul ((-989319433553 / 1000000000000 : ℝ)))).add (((hasDerivAt_id x).pow 4).const_mul ((929535157749 / 1000000000000 : ℝ)))).add (((hasDerivAt_id x).pow 5).const_mul ((-18278482591 / 25000000000 : ℝ)))).add (((hasDerivAt_id x).pow 6).const_mul ((71960568387 / 200000000000 : ℝ)))).add (((hasDerivAt_id x).pow 8).const_mul ((-97801312287 / 1000000000000 : ℝ)))).add (((hasDerivAt_id x).pow 10).const_mul ((9324153817 / 250000000000 : ℝ)))).add (((hasDerivAt_id x).pow 13).const_mul ((-111714529 / 8000000000 : ℝ)))).add (((hasDerivAt_id x).pow 14).const_mul ((6376973401 / 1000000000000 : ℝ)))) using 1 <;> (try funext y) <;> dsimp <;> ring
lemma kappa7_strictAnti : StrictAntiOn kappa7 (Set.Icc (0 : ℝ) 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc 0 1)
    (fun x _ => (kappa7_hasDerivAt x).continuousAt.continuousWithinAt)
  intro x hx
  rw [(kappa7_hasDerivAt x).deriv]
  exact kappa7_deriv_neg x (interior_subset hx)

noncomputable def pair7 (Y : ℝ) : ℝ :=
  ((214103349872601 / 10000000000000000000 : ℝ)) / (1 + Y) +
    ((-15711945772697559 / 10000000000000000000 : ℝ)) / (4 + Y) +
    ((88861547255641681 / 3000000000000000000 : ℝ)) / (9 + Y) +
    ((-2391379715826060531 / 10000000000000000000 : ℝ)) / (16 + Y) +
    ((49598848259258762671 / 50000000000000000000 : ℝ)) / (25 + Y) +
    ((-26736268392056850121 / 12000000000000000000 : ℝ)) / (36 + Y) +
    ((5037233814362823879 / 2000000000000000000 : ℝ)) / (49 + Y) +
    ((-62592896686242438747 / 80000000000000000000 : ℝ)) / (64 + Y) +
    ((-26406373258344146249 / 30000000000000000000 : ℝ)) / (81 + Y) +
    ((9324148399666632323 / 25000000000000000000 : ℝ)) / (100 + Y) +
    ((1025656427385148393 / 2500000000000000000 : ℝ)) / (121 + Y) +
    ((-188797618916141349 / 1040000000000000000 : ℝ)) / (169 + Y) +
    ((-531114148117361523 / 5000000000000000000 : ℝ)) / (196 + Y) +
    ((14348186447228454019 / 150000000000000000000 : ℝ)) / (225 + Y)

lemma pair7_from_coefficients (Y : ℝ) :
    pair7 Y = ∑ m ∈ Finset.range 15,
      (((m + 1 : ℝ) * (coefficient7 (m + 1) + coefficient7 m) -
        pairedEps ⟨6, by decide⟩ * |coefficient7 (m + 1) + coefficient7 m| / (m + 1)) /
          ((m + 1 : ℝ) ^ 2 + Y)) := by
  norm_num [pair7, coefficient7, pairedEps, Finset.sum_range_succ] 

noncomputable def numerator7 (Y : ℝ) : ℝ :=
  (1482820619316410435636292163329171456000) +
    (-5961379730048009243826109005641789399040) * Y +
    (9566149892810030586788495215126401038592) * Y ^ 2 +
    (-2989135008419917743023181233234798862336) * Y ^ 3 +
    (302264895810145379096931177586521453728) * Y ^ 4 +
    (-5815356174494332848232417777985361600) * Y ^ 5 +
    (-142821373232029079987338821141499995) * Y ^ 6 +
    (2678917442802729705114765821024760) * Y ^ 7 +
    (34725191582016234964793579918460) * Y ^ 8 +
    (-145649784604177554940330629720) * Y ^ 9 +
    (-1751232329561092162593027570) * Y ^ 10 +
    (2961924460136779116537480) * Y ^ 11 +
    (25248996271179477967548) * Y ^ 12 +
    (-21806648865888909544) * Y ^ 13 +
    (4885257898293237) * Y ^ 14

noncomputable def compact7 (x : ℝ) : ℝ :=
  (1482820619316410435636292163329171456000) +
    (-80373285970909838537169180343026294374400) * x +
    (1866531030545037610019146279109027328230400) * x ^ 2 +
    (-19658137774660575055925350863238894249881600) * x ^ 3 +
    (117573572811139784120442973972910267186393600) * x ^ 4 +
    (-451258220253094839755638758398469237268352000) * x ^ 5 +
    (1189017765827286292228154091994565974766356800) * x ^ 6 +
    (-2233923737862314830143462672124084208025484800) * x ^ 7 +
    (3051065033387802730991439244560777341543827200) * x ^ 8 +
    (-3044752445847092313823708203798974083710835200) * x ^ 9 +
    (2201194591275132010807789245471869304150576000) * x ^ 10 +
    (-1123953952131952293097589235829013407419302400) * x ^ 11 +
    (384770180198647500361055031060141181094534400) * x ^ 12 +
    (-79307311225492585754094223816278623407065600) * x ^ 13 +
    (7445021029406163465410073702565055133921600) * x ^ 14

lemma compact7_pos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < compact7 x := by
  unfold compact7
  bernstein_bound 10 (trust := kernel)

lemma compact7_identity (Y : ℝ) (hY : 0 ≤ Y) :
    (Y + 10) ^ 14 * compact7 (Y / (Y + 10)) = 10 ^ 14 * numerator7 Y := by
  have h : Y + 10 ≠ 0 := by linarith
  unfold compact7 numerator7
  field_simp
  ring

lemma numerator7_pos (Y : ℝ) (hY : 0 ≤ Y) : 0 < numerator7 Y := by
  have hd : 0 < Y + 10 := by linarith
  have hx : Y / (Y + 10) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg hY hd.le
    · exact (div_le_one hd).mpr (by linarith)
  have hp := mul_pos (pow_pos hd 14) (compact7_pos _ hx)
  rw [compact7_identity Y hY] at hp
  exact (mul_pos_iff_of_pos_left (by norm_num : (0 : ℝ) < 10 ^ 14)).mp hp

lemma pair7_identity (Y : ℝ) (hY : 0 ≤ Y) :
    (1040000000000000000000) * pair7 Y * ((1 + Y) * (4 + Y) * (9 + Y) * (16 + Y) * (25 + Y) * (36 + Y) * (49 + Y) * (64 + Y) * (81 + Y) * (100 + Y) * (121 + Y) * (144 + Y) * (169 + Y) * (196 + Y) * (225 + Y)) = numerator7 Y := by
  have h1 : (1 : ℝ) + Y ≠ 0 := by linarith
  have h2 : (4 : ℝ) + Y ≠ 0 := by linarith
  have h3 : (9 : ℝ) + Y ≠ 0 := by linarith
  have h4 : (16 : ℝ) + Y ≠ 0 := by linarith
  have h5 : (25 : ℝ) + Y ≠ 0 := by linarith
  have h6 : (36 : ℝ) + Y ≠ 0 := by linarith
  have h7 : (49 : ℝ) + Y ≠ 0 := by linarith
  have h8 : (64 : ℝ) + Y ≠ 0 := by linarith
  have h9 : (81 : ℝ) + Y ≠ 0 := by linarith
  have h10 : (100 : ℝ) + Y ≠ 0 := by linarith
  have h11 : (121 : ℝ) + Y ≠ 0 := by linarith
  have h12 : (144 : ℝ) + Y ≠ 0 := by linarith
  have h13 : (169 : ℝ) + Y ≠ 0 := by linarith
  have h14 : (196 : ℝ) + Y ≠ 0 := by linarith
  have h15 : (225 : ℝ) + Y ≠ 0 := by linarith
  unfold pair7 numerator7
  field_simp
  ring

lemma pair7_pos (Y : ℝ) (hY : 0 ≤ Y) : 0 < pair7 Y := by
  have hp := numerator7_pos Y hY
  rw [← pair7_identity Y hY] at hp
  have hd : 0 < ((1 + Y) * (4 + Y) * (9 + Y) * (16 + Y) * (25 + Y) * (36 + Y) * (49 + Y) * (64 + Y) * (81 + Y) * (100 + Y) * (121 + Y) * (144 + Y) * (169 + Y) * (196 + Y) * (225 + Y) : ℝ) := by positivity
  have hs : (0 : ℝ) < 1040000000000000000000 := by norm_num
  have hm : 0 < (1040000000000000000000) * pair7 Y := (mul_pos_iff_of_pos_right hd).mp hp
  exact (mul_pos_iff_of_pos_left hs).mp hm

#print axioms pair7_pos

end Multiplier
end Varlamov
