import Superfusion.GaugeChi.TripleCerts.G5_1
import Superfusion.GaugeChi.TripleCerts.G5_15
import Superfusion.GaugeChi.TripleCerts.G5_16
import Superfusion.GaugeChi.TripleCerts.G5_17
import Superfusion.GaugeChi.TripleCerts.G5_2
import Superfusion.RMod.Constructive.RawSemanticConnectorBridge

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Superfusion
namespace RModCoordinate
namespace RawSemanticSkeletalData

open GaugeChi
open RawSemanticConnector

/-- Raw connector membership at fixed labels (5,2). -/
theorem forward_mem_five_two : ∀ c : ZMod 8,
    gtOfTNative ℝ realGauge 5 2 c (forwardMatrix 5 2 c) ∈
      gInterSpace ℝ realGauge 5 2 c (parity 5 2 c) :=
  zmod8Rec
    (memOfAlignedCoeff TripleCerts.G5_15.gtOfT5_2_0_mem_gInterSpace (by decide)
      TripleCerts.G5_15.TL5_2_0 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G5_16.gtOfT5_2_1_mem_gInterSpace (by decide)
      TripleCerts.G5_16.TL5_2_1 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G5_16.gtOfT5_2_2_mem_gInterSpace (by decide)
      TripleCerts.G5_16.TL5_2_2 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G5_1.gtOfT5_2_3_mem_gInterSpace (by decide)
      TripleCerts.G5_1.TL5_2_3 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G5_16.gtOfT5_2_4_mem_gInterSpace (by decide)
      TripleCerts.G5_16.TL5_2_4 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G5_2.gtOfT5_2_5_mem_gInterSpace (by decide)
      TripleCerts.G5_2.TL5_2_5 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G5_16.gtOfT5_2_6_mem_gInterSpace (by decide)
      TripleCerts.G5_16.TL5_2_6 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G5_17.gtOfT5_2_7_mem_gInterSpace (by decide)
      TripleCerts.G5_17.TL5_2_7 (by rfl) (by rfl))

end RawSemanticSkeletalData
end RModCoordinate
end Superfusion

