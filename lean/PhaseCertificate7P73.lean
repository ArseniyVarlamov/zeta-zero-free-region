import PrimeNumberTheoremAnd.IEANTN.Varlamov.PhaseSOS

namespace Varlamov.PhaseCertificate7P73
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000

def weights : List ℤ := [136169074931, 1904116255, 26242597, 361250, 4967, 67, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def factor : List ℤ := [2724421217497, 5024785868049, 7667341815199, 5850130198740, 3502446194726, 210514649709, -160502056416, -139746229917, 201160876052, 39850415669, -43045146258, 8512908321, 9769110971, -2661897375, 4683641750, -3954302964, 2627951840, -338026830, -396591976, 760553015, -403017116, -195807053, 457754613, -362392390, 198275839, -1341087, -5798642, 10023383, 414954, -15169627, 14094401, 2835917, -14399477, 9239814, 1403433, -4255469, 2297931, -99272, 136491, 35650, -173070, 75759, 103115, -109511, -19901, 63265, 19996, -59831, 30781, 1652, 338, -1969, 1609, -165, -764, 1023, -1153, 875, 261, -836, 465, 2, -30, 28, 5, -31, 24, 2, -16, 12, 4, -11, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def target : ℤ := 15839

/-- Exact integer SOS residual certificate; numerical search is untrusted. -/
lemma sos_check : PhaseSOS.check 240 weights factor target = true := by decide +kernel

theorem rounded_lower_bound (x : ℝ) :
    (((target - 1 : ℤ) : ℝ) / PhaseSOS.targetScale) ≤ PhaseSOS.roundedPhase weights x :=
  PhaseSOS.checked_lower_bound 240 weights factor target sos_check x

#print axioms rounded_lower_bound
end Varlamov.PhaseCertificate7P73
