import PrimeNumberTheoremAnd.IEANTN.Varlamov.PhaseSOS

namespace Varlamov.PhaseCertificate4P19
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000

def weights : List ℤ := [502498992759, 27927348062, 1480513458, 78235248, 4131022, 217990, 11495, 604, 30, 0]
def factor : List ℤ := [7806826704618, 10298654920440, 15504493926354, 9432265604408, 5808239795635, -704211359315, 528747229288, -259604093738, 379782057214, 78005414880, -57095114517, 17983498812, 14015506755, -7332703378, 16921124308, -13393442939, 10579451633, -1807946905, 1407693609, 1656409227, -3159749178, 1049151539, 1575109885, -1834955146, 1211153664, 77572140, 103401554, -45097727, -82571951, -18051683, 200869205, -100756042, -142418370, 174555532, -5957098, -63226198, 38821146, 6187435, 6385390, -7791417, -4735719, 9592512, 1317722, -8825931, 2492773, 4602452, -668992, -3471957, 2466225, 306155, -90709, -346302, 383115, -1627, -240174, 155362, -110772, 210991, -31634, -163298, 131955, -7953, -6412, 19248, -7022, -16178, 20341, -4756, -7416, 11328, -922, -8335, 5720, -510, 1648, -431, -1207, 884, 372, -320, -381, 636, -34, -505, 298, 77, 10, -66, 28, 10, 16, -16, -18, 34, -5, -27, 21, 0, -2, 1, -1, 0, 1, -1, -1, 2, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def target : ℤ := 890360

/-- Exact integer SOS residual certificate; numerical search is untrusted. -/
lemma sos_check : PhaseSOS.check 120 weights factor target = true := by decide +kernel

theorem rounded_lower_bound (x : ℝ) :
    (((target - 1 : ℤ) : ℝ) / PhaseSOS.targetScale) ≤ PhaseSOS.roundedPhase weights x :=
  PhaseSOS.checked_lower_bound 120 weights factor target sos_check x

#print axioms rounded_lower_bound
end Varlamov.PhaseCertificate4P19
