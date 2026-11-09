import PrimeNumberTheoremAnd.IEANTN.Varlamov.PhaseSOS

namespace Varlamov.PhaseCertificate2P19
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000

def weights : List ℤ := [502876017055, 27967141500, 1481760977, 78183883, 4118601, 216642, 11378, 595, 30, 0]
def factor : List ℤ := [7810596168628, 10302314753937, 15510966160852, 9435042496119, 5810679217192, -704854269101, 529389521787, -259799662993, 380046327607, 78007282329, -57115905492, 18012856994, 14004367621, -7336911813, 16933901675, -13403341981, 10588825278, -1809424513, 1408163420, 1657928990, -3161611054, 1049457599, 1576033491, -1835990321, 1212202742, 77468416, 103405387, -44979853, -82651906, -18099189, 200943799, -100766149, -142484467, 174622445, -5977154, -63243834, 38850855, 6176141, 6378059, -7780386, -4731437, 9582964, 1313046, -8814873, 2491163, 4596193, -668887, -3466693, 2463232, 305066, -90504, -345005, 381806, -1733, -239240, 154790, -110413, 210315, -31563, -162734, 131488, -7902, -6366, 19119, -6981, -16062, 20203, -4731, -7361, 11256, -921, -8281, 5686, -504, 1630, -427, -1194, 875, 368, -317, -376, 629, -34, -500, 295, 76, 10, -65, 27, 9, 16, -16, -18, 34, -5, -26, 21, 0, -2, 1, -1, 0, 1, -1, -1, 2, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def target : ℤ := 890727

/-- Exact integer SOS residual certificate; numerical search is untrusted. -/
lemma sos_check : PhaseSOS.check 120 weights factor target = true := by decide +kernel

theorem rounded_lower_bound (x : ℝ) :
    (((target - 1 : ℤ) : ℝ) / PhaseSOS.targetScale) ≤ PhaseSOS.roundedPhase weights x :=
  PhaseSOS.checked_lower_bound 120 weights factor target sos_check x

#print axioms rounded_lower_bound
end Varlamov.PhaseCertificate2P19
