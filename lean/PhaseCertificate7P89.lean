import PrimeNumberTheoremAnd.IEANTN.Varlamov.PhaseSOS

namespace Varlamov.PhaseCertificate7P89
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000

def weights : List ℤ := [112003846939, 1281860661, 14491911, 163638, 1844, 19, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def factor : List ℤ := [2354508822993, 4504685565557, 6902568950253, 5401508786578, 3237329774369, 261831199207, -177249302696, -132818388016, 181753067433, 40213954364, -40519300504, 6567630650, 9673631789, -2281131546, 3890237373, -3267528098, 2091440910, -221457609, -383381901, 620764100, -287148119, -189633503, 375445856, -287053795, 151377259, -146261, -5152213, 6748996, 1432477, -10857455, 8898200, 2695216, -9749524, 5855764, 1097691, -2831976, 1486670, -62188, 67040, 30309, -93790, 33053, 58805, -55079, -13807, 32402, 12831, -32448, 16191, 729, 194, -901, 722, -78, -351, 491, -536, 369, 140, -372, 198, 2, -11, 9, 3, -11, 8, 1, -6, 4, 1, -4, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def target : ℤ := 8322

/-- Exact integer SOS residual certificate; numerical search is untrusted. -/
lemma sos_check : PhaseSOS.check 240 weights factor target = true := by decide +kernel

theorem rounded_lower_bound (x : ℝ) :
    (((target - 1 : ℤ) : ℝ) / PhaseSOS.targetScale) ≤ PhaseSOS.roundedPhase weights x :=
  PhaseSOS.checked_lower_bound 240 weights factor target sos_check x

#print axioms rounded_lower_bound
end Varlamov.PhaseCertificate7P89
