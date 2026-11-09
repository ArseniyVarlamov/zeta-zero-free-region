import PrimeNumberTheoremAnd.IEANTN.Varlamov.PhaseSOS

namespace Varlamov.PhaseCertificate7P79
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000

def weights : List ℤ := [125975611406, 1626293875, 20712036, 263469, 3347, 41, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def factor : List ℤ := [2569625040573, 4810659820547, 7352916557606, 5668495833138, 3394955264843, 232799552342, -168394026581, -136919083320, 193240125252, 40004001498, -42049899037, 7715071235, 9737990655, -2502462008, 4350653160, -3667801763, 2401734192, -287832681, -393920750, 702562172, -352764098, -194570668, 423234550, -330351256, 178096797, -791216, -5617004, 8608075, 938193, -13318788, 11758629, 2830577, -12342425, 7711259, 1277803, -3620236, 1933285, -83085, 103207, 34501, -135891, 54711, 82655, -83370, -17433, 48525, 16839, -46908, 23833, 1195, 273, -1443, 1170, -124, -559, 764, -851, 621, 205, -606, 331, 2, -21, 18, 4, -21, 16, 2, -10, 8, 3, -7, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def target : ℤ := 12306

/-- Exact integer SOS residual certificate; numerical search is untrusted. -/
lemma sos_check : PhaseSOS.check 240 weights factor target = true := by decide +kernel

theorem rounded_lower_bound (x : ℝ) :
    (((target - 1 : ℤ) : ℝ) / PhaseSOS.targetScale) ≤ PhaseSOS.roundedPhase weights x :=
  PhaseSOS.checked_lower_bound 240 weights factor target sos_check x

#print axioms rounded_lower_bound
end Varlamov.PhaseCertificate7P79
