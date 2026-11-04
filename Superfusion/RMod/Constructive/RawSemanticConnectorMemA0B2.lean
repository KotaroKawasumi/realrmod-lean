import Superfusion.GaugeChi.TripleCerts.G0_1
import Superfusion.RMod.Constructive.RawSemanticConnectorBridge

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Superfusion
namespace RModCoordinate
namespace RawSemanticSkeletalData

open GaugeChi
open RawSemanticConnector

/-- Raw connector membership at fixed labels (0,2). -/
theorem forward_mem_zero_two : ∀ c : ZMod 8,
    gtOfTNative ℝ realGauge 0 2 c (forwardMatrix 0 2 c) ∈
      gInterSpace ℝ realGauge 0 2 c (parity 0 2 c) :=
  zmod8Rec
    (memOfAlignedCoeff TripleCerts.G0_1.gtOfT0_2_0_mem_gInterSpace (by decide)
      TripleCerts.G0_1.TL0_2_0 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G0_1.gtOfT0_2_1_mem_gInterSpace (by decide)
      TripleCerts.G0_1.TL0_2_1 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G0_1.gtOfT0_2_2_mem_gInterSpace (by decide)
      TripleCerts.G0_1.TL0_2_2 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G0_1.gtOfT0_2_3_mem_gInterSpace (by decide)
      TripleCerts.G0_1.TL0_2_3 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G0_1.gtOfT0_2_4_mem_gInterSpace (by decide)
      TripleCerts.G0_1.TL0_2_4 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G0_1.gtOfT0_2_5_mem_gInterSpace (by decide)
      TripleCerts.G0_1.TL0_2_5 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G0_1.gtOfT0_2_6_mem_gInterSpace (by decide)
      TripleCerts.G0_1.TL0_2_6 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G0_1.gtOfT0_2_7_mem_gInterSpace (by decide)
      TripleCerts.G0_1.TL0_2_7 (by rfl) (by rfl))

end RawSemanticSkeletalData
end RModCoordinate
end Superfusion

