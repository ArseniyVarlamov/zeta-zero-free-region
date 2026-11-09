import PrimeNumberTheoremAnd.IEANTN.Varlamov.PhaseSOS

namespace Varlamov.PhaseCertificate3P19
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000

def weights : List ℤ := [502668568825, 27946788627, 1481572744, 78274070, 4131252, 217859, 11478, 603, 30, 0]
def factor : List ℤ := [7808816443468, 10300372965627, 15507385977112, 9433397371185, 5809190710675, -704575078420, 529123186311, -259690763897, 379877174247, 78026060543, -57102082310, 17989134216, 14015247314, -7334353715, 16927174448, -13398156458, 10583659368, -1808426856, 1408516672, 1656683152, -3160987720, 1049811172, 1575558157, -1835636699, 1211710904, 77612550, 103445275, -45126121, -82613409, -18035451, 200943017, -100812966, -142466697, 174635338, -5968592, -63252242, 38842632, 6189437, 6385505, -7793656, -4735606, 9595250, 1316306, -8827656, 2494231, 4603206, -669610, -3472329, 2466839, 306058, -90743, -346178, 383041, -1656, -240111, 155317, -110728, 210952, -31648, -163255, 131924, -7946, -6403, 19229, -7018, -16160, 20322, -4754, -7407, 11319, -923, -8328, 5716, -508, 1645, -430, -1205, 883, 371, -319, -380, 635, -34, -504, 297, 77, 10, -66, 28, 10, 16, -16, -18, 34, -5, -27, 21, 0, -2, 1, -1, 0, 1, -1, -1, 2, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def target : ℤ := 890895

/-- Exact integer SOS residual certificate; numerical search is untrusted. -/
lemma sos_check : PhaseSOS.check 120 weights factor target = true := by decide +kernel

theorem rounded_lower_bound (x : ℝ) :
    (((target - 1 : ℤ) : ℝ) / PhaseSOS.targetScale) ≤ PhaseSOS.roundedPhase weights x :=
  PhaseSOS.checked_lower_bound 120 weights factor target sos_check x

#print axioms rounded_lower_bound
end Varlamov.PhaseCertificate3P19
