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

/-- Raw connector membership at fixed labels (0,1). -/
theorem forward_mem_zero_one : ∀ c : ZMod 8,
    gtOfTNative ℝ realGauge 0 1 c (forwardMatrix 0 1 c) ∈
      gInterSpace ℝ realGauge 0 1 c (parity 0 1 c) :=
  zmod8Rec
    (memOfAlignedCoeff TripleCerts.G0_1.gtOfT0_1_0_mem_gInterSpace (by decide)
      TripleCerts.G0_1.TL0_1_0 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G0_1.gtOfT0_1_1_mem_gInterSpace (by decide)
      TripleCerts.G0_1.TL0_1_1 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G0_1.gtOfT0_1_2_mem_gInterSpace (by decide)
      TripleCerts.G0_1.TL0_1_2 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G0_1.gtOfT0_1_3_mem_gInterSpace (by decide)
      TripleCerts.G0_1.TL0_1_3 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G0_1.gtOfT0_1_4_mem_gInterSpace (by decide)
      TripleCerts.G0_1.TL0_1_4 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G0_1.gtOfT0_1_5_mem_gInterSpace (by decide)
      TripleCerts.G0_1.TL0_1_5 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G0_1.gtOfT0_1_6_mem_gInterSpace (by decide)
      TripleCerts.G0_1.TL0_1_6 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G0_1.gtOfT0_1_7_mem_gInterSpace (by decide)
      TripleCerts.G0_1.TL0_1_7 (by rfl) (by rfl))

end RawSemanticSkeletalData
end RModCoordinate
end Superfusion

