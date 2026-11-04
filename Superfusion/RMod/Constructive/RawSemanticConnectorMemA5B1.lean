import Superfusion.GaugeChi.TripleCerts.G5_14
import Superfusion.GaugeChi.TripleCerts.G5_15
import Superfusion.RMod.Constructive.RawSemanticConnectorBridge

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Superfusion
namespace RModCoordinate
namespace RawSemanticSkeletalData

open GaugeChi
open RawSemanticConnector

/-- Raw connector membership at fixed labels (5,1). -/
theorem forward_mem_five_one : ∀ c : ZMod 8,
    gtOfTNative ℝ realGauge 5 1 c (forwardMatrix 5 1 c) ∈
      gInterSpace ℝ realGauge 5 1 c (parity 5 1 c) :=
  zmod8Rec
    (memOfAlignedCoeff TripleCerts.G5_14.gtOfT5_1_0_mem_gInterSpace (by decide)
      TripleCerts.G5_14.TL5_1_0 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G5_14.gtOfT5_1_1_mem_gInterSpace (by decide)
      TripleCerts.G5_14.TL5_1_1 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G5_14.gtOfT5_1_2_mem_gInterSpace (by decide)
      TripleCerts.G5_14.TL5_1_2 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G5_15.gtOfT5_1_3_mem_gInterSpace (by decide)
      TripleCerts.G5_15.TL5_1_3 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G5_15.gtOfT5_1_4_mem_gInterSpace (by decide)
      TripleCerts.G5_15.TL5_1_4 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G5_15.gtOfT5_1_5_mem_gInterSpace (by decide)
      TripleCerts.G5_15.TL5_1_5 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G5_15.gtOfT5_1_6_mem_gInterSpace (by decide)
      TripleCerts.G5_15.TL5_1_6 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G5_15.gtOfT5_1_7_mem_gInterSpace (by decide)
      TripleCerts.G5_15.TL5_1_7 (by rfl) (by rfl))

end RawSemanticSkeletalData
end RModCoordinate
end Superfusion

