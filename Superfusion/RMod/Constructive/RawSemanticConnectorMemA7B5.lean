import Superfusion.GaugeChi.TripleCerts.G7_3
import Superfusion.GaugeChi.TripleCerts.G7_4
import Superfusion.RMod.Constructive.RawSemanticConnectorBridge

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Superfusion
namespace RModCoordinate
namespace RawSemanticSkeletalData

open GaugeChi
open RawSemanticConnector

/-- Raw connector membership at fixed labels (7,5). -/
theorem forward_mem_seven_five : ∀ c : ZMod 8,
    gtOfTNative ℝ realGauge 7 5 c (forwardMatrix 7 5 c) ∈
      gInterSpace ℝ realGauge 7 5 c (parity 7 5 c) :=
  zmod8Rec
    (memOfAlignedCoeff TripleCerts.G7_3.gtOfT7_5_0_mem_gInterSpace (by decide)
      TripleCerts.G7_3.TL7_5_0 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G7_3.gtOfT7_5_1_mem_gInterSpace (by decide)
      TripleCerts.G7_3.TL7_5_1 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G7_3.gtOfT7_5_2_mem_gInterSpace (by decide)
      TripleCerts.G7_3.TL7_5_2 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G7_4.gtOfT7_5_3_mem_gInterSpace (by decide)
      TripleCerts.G7_4.TL7_5_3 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G7_4.gtOfT7_5_4_mem_gInterSpace (by decide)
      TripleCerts.G7_4.TL7_5_4 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G7_4.gtOfT7_5_5_mem_gInterSpace (by decide)
      TripleCerts.G7_4.TL7_5_5 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G7_4.gtOfT7_5_6_mem_gInterSpace (by decide)
      TripleCerts.G7_4.TL7_5_6 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G7_4.gtOfT7_5_7_mem_gInterSpace (by decide)
      TripleCerts.G7_4.TL7_5_7 (by rfl) (by rfl))

end RawSemanticSkeletalData
end RModCoordinate
end Superfusion

