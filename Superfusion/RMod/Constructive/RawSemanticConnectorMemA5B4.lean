import Superfusion.GaugeChi.TripleCerts.Exceptional
import Superfusion.GaugeChi.TripleCerts.G5_17
import Superfusion.GaugeChi.TripleCerts.G5_18
import Superfusion.GaugeChi.TripleCerts.G5_6
import Superfusion.GaugeChi.TripleCerts.G5_7
import Superfusion.RMod.Constructive.RawSemanticConnectorBridge

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Superfusion
namespace RModCoordinate
namespace RawSemanticSkeletalData

open GaugeChi
open RawSemanticConnector

/-- Raw connector membership at fixed labels (5,4). -/
theorem forward_mem_five_four : ∀ c : ZMod 8,
    gtOfTNative ℝ realGauge 5 4 c (forwardMatrix 5 4 c) ∈
      gInterSpace ℝ realGauge 5 4 c (parity 5 4 c) :=
  zmod8Rec
    (memOfAlignedCoeff TripleCerts.G5_17.gtOfT5_4_0_mem_gInterSpace (by decide)
      TripleCerts.G5_17.TL5_4_0 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G5_18.gtOfT5_4_1_mem_gInterSpace (by decide)
      TripleCerts.G5_18.TL5_4_1 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G5_18.gtOfT5_4_2_mem_gInterSpace (by decide)
      TripleCerts.G5_18.TL5_4_2 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G5_6.gtOfT5_4_3_mem_gInterSpace (by decide)
      TripleCerts.G5_6.TL5_4_3 (by rfl) (by rfl))
    (memOfNativeCoeff TripleCerts.Exceptional.gtOfTNative5_4_4_mem_gInterSpace (by decide)
      TripleCerts.Exceptional.TL5_4_4 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G5_7.gtOfT5_4_5_mem_gInterSpace (by decide)
      TripleCerts.G5_7.TL5_4_5 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G5_18.gtOfT5_4_6_mem_gInterSpace (by decide)
      TripleCerts.G5_18.TL5_4_6 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G5_18.gtOfT5_4_7_mem_gInterSpace (by decide)
      TripleCerts.G5_18.TL5_4_7 (by rfl) (by rfl))

end RawSemanticSkeletalData
end RModCoordinate
end Superfusion

