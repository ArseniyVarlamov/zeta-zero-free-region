import PrimeNumberTheoremAnd.IEANTN.Varlamov.PhaseSOS

namespace Varlamov.PhaseCertificate5P19
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000

def weights : List ℤ := [502453450536, 27921516757, 1480282676, 78236306, 4132223, 218136, 11508, 605, 30, 0]
def factor : List ℤ := [7806296363716, 10298214932723, 15503685966951, 9431975189341, 5807952747497, -704106653015, 528637935276, -259576131975, 379748242631, 78003323813, -57092949897, 17980143484, 14016826704, -7332180969, 16919260835, -13391994138, 10578089020, -1807760097, 1407540955, 1656250444, -3159431706, 1049037548, 1574978027, -1834781475, 1210989536, 77576550, 103395504, -45104777, -82558947, -18050419, 200853814, -100747560, -142407138, 174539763, -5953575, -63221561, 38815793, 6188209, 6386111, -7792158, -4736190, 9593082, 1318381, -8826790, 2492734, 4602964, -668913, -3472427, 2466439, 306271, -90723, -346443, 383250, -1613, -240272, 155423, -110813, 211061, -31639, -163357, 132003, -7959, -6418, 19263, -7026, -16192, 20356, -4759, -7423, 11336, -922, -8341, 5723, -510, 1650, -431, -1209, 885, 372, -320, -381, 637, -34, -506, 298, 77, 10, -66, 28, 10, 16, -16, -18, 34, -5, -27, 21, 0, -2, 1, -1, 0, 1, -1, -1, 2, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def target : ℤ := 890271

/-- Exact integer SOS residual certificate; numerical search is untrusted. -/
lemma sos_check : PhaseSOS.check 120 weights factor target = true := by decide +kernel

theorem rounded_lower_bound (x : ℝ) :
    (((target - 1 : ℤ) : ℝ) / PhaseSOS.targetScale) ≤ PhaseSOS.roundedPhase weights x :=
  PhaseSOS.checked_lower_bound 120 weights factor target sos_check x

#print axioms rounded_lower_bound
end Varlamov.PhaseCertificate5P19
