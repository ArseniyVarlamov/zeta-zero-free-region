import PrimeNumberTheoremAnd.IEANTN.Varlamov.PhaseSOS

namespace Varlamov.PhaseCertificate7P83
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000

def weights : List ℤ := [119988144873, 1473557530, 17862801, 216278, 2614, 30, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def factor : List ℤ := [2477877946709, 4681398715471, 7162839711629, 5556817834733, 3328983107564, 245482757110, -172483170888, -135200233420, 188413225125, 40096438481, -41419599302, 7231032111, 9713985699, -2408057281, 4153996189, -3497395350, 2268772287, -259005384, -390403756, 667831375, -324171166, -192919572, 402824644, -311707566, 166509363, -497856, -5446459, 7797635, 1181067, -12251398, 10484201, 2789631, -11198584, 6882417, 1201568, -3270757, 1734378, -73897, 86432, 33010, -116634, 44487, 71847, -70241, -15895, 41070, 15071, -40273, 20307, 974, 237, -1187, 958, -103, -461, 636, -703, 501, 176, -495, 268, 2, -16, 14, 4, -16, 12, 1, -8, 6, 2, -6, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def target : ℤ := 10483

/-- Exact integer SOS residual certificate; numerical search is untrusted. -/
lemma sos_check : PhaseSOS.check 240 weights factor target = true := by decide +kernel

theorem rounded_lower_bound (x : ℝ) :
    (((target - 1 : ℤ) : ℝ) / PhaseSOS.targetScale) ≤ PhaseSOS.roundedPhase weights x :=
  PhaseSOS.checked_lower_bound 240 weights factor target sos_check x

#print axioms rounded_lower_bound
end Varlamov.PhaseCertificate7P83
