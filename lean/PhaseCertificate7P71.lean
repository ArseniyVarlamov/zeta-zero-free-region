import PrimeNumberTheoremAnd.IEANTN.Varlamov.PhaseSOS

namespace Varlamov.PhaseCertificate7P71
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000

def weights : List ℤ := [139943999550, 2012712562, 28520344, 403661, 5706, 79, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def factor : List ℤ := [2781332194952, 5102306346034, 7781055719083, 5914889535607, 3540841618663, 202069798546, -157300648992, -140767900867, 204006304826, 39797260239, -43391086482, 8800065093, 9778090020, -2720585987, 4806472370, -4059309001, 2711649591, -356919499, -396552927, 781656821, -422114015, -195768478, 470468225, -374352341, 205887658, -1558437, -5828801, 10555644, 185640, -15863219, 15011929, 2815944, -15195486, 9843714, 1448409, -4503568, 2441298, -105363, 150412, 35531, -188291, 84824, 111355, -120489, -20740, 69420, 21204, -65165, 33677, 1851, 364, -2196, 1799, -182, -853, 1133, -1281, 987, 284, -935, 524, 2, -34, 32, 5, -36, 28, 2, -18, 14, 4, -13, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def target : ℤ := 17292

/-- Exact integer SOS residual certificate; numerical search is untrusted. -/
lemma sos_check : PhaseSOS.check 240 weights factor target = true := by decide +kernel

theorem rounded_lower_bound (x : ℝ) :
    (((target - 1 : ℤ) : ℝ) / PhaseSOS.targetScale) ≤ PhaseSOS.roundedPhase weights x :=
  PhaseSOS.checked_lower_bound 240 weights factor target sos_check x

#print axioms rounded_lower_bound
end Varlamov.PhaseCertificate7P71
