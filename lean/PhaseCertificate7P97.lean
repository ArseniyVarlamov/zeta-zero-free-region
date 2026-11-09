import PrimeNumberTheoremAnd.IEANTN.Varlamov.PhaseSOS

namespace Varlamov.PhaseCertificate7P97
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000

def weights : List ℤ := [102877439105, 1079432588, 11197393, 116012, 1199, 11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def factor : List ℤ := [2211858361965, 4295992469829, 6594569739718, 5214108496067, 3126856763918, 279594254317, -181657228716, -129943523353, 173799208771, 40328228780, -39396910102, 5784263429, 9613067147, -2134232531, 3586249073, -3000964006, 1888941806, -180052964, -371962583, 565975210, -246473498, -184322725, 343923121, -259184623, 134554914, 192731, -4732653, 5607291, 1621035, -9315518, 7246428, 2536814, -8203330, 4791429, 976757, -2368755, 1228028, -49778, 48735, 26528, -71460, 22720, 45775, -40743, -11444, 24138, 10461, -24839, 12241, 509, 150, -641, 509, -55, -252, 356, -382, 252, 106, -262, 137, 2, -7, 6, 2, -7, 5, 1, -4, 2, 1, -2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def target : ℤ := 6208

/-- Exact integer SOS residual certificate; numerical search is untrusted. -/
lemma sos_check : PhaseSOS.check 240 weights factor target = true := by decide +kernel

theorem rounded_lower_bound (x : ℝ) :
    (((target - 1 : ℤ) : ℝ) / PhaseSOS.targetScale) ≤ PhaseSOS.roundedPhase weights x :=
  PhaseSOS.checked_lower_bound 240 weights factor target sos_check x

#print axioms rounded_lower_bound
end Varlamov.PhaseCertificate7P97
