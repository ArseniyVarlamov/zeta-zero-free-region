import PrimeNumberTheoremAnd.IEANTN.Varlamov.PhaseSOS

namespace Varlamov.PhaseCertificate1P19
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000

def weights : List ℤ := [503185919211, 27974782530, 1477662886, 77564192, 4056594, 211429, 10981, 567, 28, 0]
def factor : List ℤ := [7810243308950, 10304644533096, 15516164939150, 9438946488840, 5814071464101, -704437076858, 528811187425, -259927256431, 380446652425, 77821611430, -57157898298, 18102858797, 13954968533, -7342081993, 16938202988, -13406426015, 10593893788, -1812140580, 1402432658, 1662879759, -3158773219, 1044482153, 1576294588, -1834485533, 1211905137, 76561289, 103006603, -44121398, -82644353, -18498979, 200600763, -100257984, -142346384, 174174445, -5959815, -63078406, 38785755, 6101703, 6342103, -7705051, -4712402, 9510088, 1304653, -8744655, 2468907, 4558614, -662225, -3437670, 2442724, 300753, -89167, -339951, 376174, -1937, -235335, 152449, -109100, 207423, -31079, -160419, 129520, -7720, -6228, 18677, -6820, -15676, 19722, -4628, -7182, 10996, -907, -8090, 5561, -487, 1574, -411, -1152, 844, 355, -305, -363, 608, -33, -482, 285, 73, 9, -62, 26, 9, 15, -15, -17, 32, -5, -25, 20, 0, -1, 1, 0, 0, 1, -1, -1, 2, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def target : ℤ := 887417

/-- Exact integer SOS residual certificate; numerical search is untrusted. -/
lemma sos_check : PhaseSOS.check 120 weights factor target = true := by decide +kernel

theorem rounded_lower_bound (x : ℝ) :
    (((target - 1 : ℤ) : ℝ) / PhaseSOS.targetScale) ≤ PhaseSOS.roundedPhase weights x :=
  PhaseSOS.checked_lower_bound 120 weights factor target sos_check x

#print axioms rounded_lower_bound
end Varlamov.PhaseCertificate1P19
