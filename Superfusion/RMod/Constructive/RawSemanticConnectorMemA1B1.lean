import Superfusion.GaugeChi.TripleCerts.Generic1
import Superfusion.RMod.Constructive.RawSemanticConnectorBridge

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Superfusion
namespace RModCoordinate
namespace RawSemanticSkeletalData

open GaugeChi
open RawSemanticConnector

/-- Raw connector membership at fixed labels (1,1). -/
theorem forward_mem_one_one : ∀ c : ZMod 8,
    gtOfTNative ℝ realGauge 1 1 c (forwardMatrix 1 1 c) ∈
      gInterSpace ℝ realGauge 1 1 c (parity 1 1 c) :=
  zmod8Rec
    (memOfAlignedCoeff TripleCerts.Generic1.gtOfT1_1_0_mem_gInterSpace (by decide)
      TripleCerts.Generic1.TL1_1_0 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.Generic1.gtOfT1_1_1_mem_gInterSpace (by decide)
      TripleCerts.Generic1.TL1_1_1 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.Generic1.gtOfT1_1_2_mem_gInterSpace (by decide)
      TripleCerts.Generic1.TL1_1_2 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.Generic1.gtOfT1_1_3_mem_gInterSpace (by decide)
      TripleCerts.Generic1.TL1_1_3 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.Generic1.gtOfT1_1_4_mem_gInterSpace (by decide)
      TripleCerts.Generic1.TL1_1_4 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.Generic1.gtOfT1_1_5_mem_gInterSpace (by decide)
      TripleCerts.Generic1.TL1_1_5 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.Generic1.gtOfT1_1_6_mem_gInterSpace (by decide)
      TripleCerts.Generic1.TL1_1_6 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.Generic1.gtOfT1_1_7_mem_gInterSpace (by decide)
      TripleCerts.Generic1.TL1_1_7 (by rfl) (by rfl))

end RawSemanticSkeletalData
end RModCoordinate
end Superfusion

