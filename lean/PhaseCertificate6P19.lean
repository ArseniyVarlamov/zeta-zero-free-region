import PrimeNumberTheoremAnd.IEANTN.Varlamov.PhaseSOS

namespace Varlamov.PhaseCertificate6P19
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000

def weights : List ℤ := [502407254115, 27916012053, 1479926327, 78217284, 4131365, 218107, 11508, 606, 31, 0]
def factor : List ℤ := [7805712793167, 10297735558961, 15502901009234, 9431684326116, 5807714595150, -703997385977, 528523627775, -259552792033, 379725653769, 77995011482, -57091387727, 17979643800, 14016246664, -7331762563, 16917573268, -13390675825, 10576943704, -1807655322, 1407235568, 1656231231, -3159040920, 1048787627, 1574851585, -1834566793, 1210826160, 77553672, 103378074, -45085958, -82547112, -18059871, 200828350, -100725026, -142391483, 174511324, -5950107, -63212029, 38808838, 6186705, 6385623, -7790573, -4735978, 9591384, 1318675, -8825411, 2492038, 4602274, -668653, -3471954, 2466004, 306245, -90695, -346415, 383199, -1605, -240241, 155405, -110807, 211036, -31629, -163341, 131987, -7958, -6419, 19263, -7025, -16192, 20356, -4758, -7423, 11336, -922, -8341, 5723, -511, 1650, -431, -1209, 885, 373, -320, -381, 637, -33, -506, 298, 78, 10, -66, 28, 10, 16, -16, -18, 34, -5, -27, 21, 0, -2, 1, -1, 0, 1, -1, -1, 2, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def target : ℤ := 890075

/-- Exact integer SOS residual certificate; numerical search is untrusted. -/
lemma sos_check : PhaseSOS.check 120 weights factor target = true := by decide +kernel

theorem rounded_lower_bound (x : ℝ) :
    (((target - 1 : ℤ) : ℝ) / PhaseSOS.targetScale) ≤ PhaseSOS.roundedPhase weights x :=
  PhaseSOS.checked_lower_bound 120 weights factor target sos_check x

#print axioms rounded_lower_bound
end Varlamov.PhaseCertificate6P19
