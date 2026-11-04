import Superfusion.GaugeChi.TripleCerts.Exceptional
import Superfusion.GaugeChi.TripleCerts.G3_17
import Superfusion.GaugeChi.TripleCerts.G3_18
import Superfusion.GaugeChi.TripleCerts.G3_7
import Superfusion.GaugeChi.TripleCerts.G3_8
import Superfusion.RMod.Constructive.RawSemanticConnectorBridge

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Superfusion
namespace RModCoordinate
namespace RawSemanticSkeletalData

open GaugeChi
open RawSemanticConnector

/-- Raw connector membership at fixed labels (3,4). -/
theorem forward_mem_three_four : ∀ c : ZMod 8,
    gtOfTNative ℝ realGauge 3 4 c (forwardMatrix 3 4 c) ∈
      gInterSpace ℝ realGauge 3 4 c (parity 3 4 c) :=
  zmod8Rec
    (memOfAlignedCoeff TripleCerts.G3_17.gtOfT3_4_0_mem_gInterSpace (by decide)
      TripleCerts.G3_17.TL3_4_0 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G3_18.gtOfT3_4_1_mem_gInterSpace (by decide)
      TripleCerts.G3_18.TL3_4_1 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G3_18.gtOfT3_4_2_mem_gInterSpace (by decide)
      TripleCerts.G3_18.TL3_4_2 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G3_7.gtOfT3_4_3_mem_gInterSpace (by decide)
      TripleCerts.G3_7.TL3_4_3 (by rfl) (by rfl))
    (memOfNativeCoeff TripleCerts.Exceptional.gtOfTNative3_4_4_mem_gInterSpace (by decide)
      TripleCerts.Exceptional.TL3_4_4 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G3_8.gtOfT3_4_5_mem_gInterSpace (by decide)
      TripleCerts.G3_8.TL3_4_5 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G3_18.gtOfT3_4_6_mem_gInterSpace (by decide)
      TripleCerts.G3_18.TL3_4_6 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G3_18.gtOfT3_4_7_mem_gInterSpace (by decide)
      TripleCerts.G3_18.TL3_4_7 (by rfl) (by rfl))

end RawSemanticSkeletalData
end RModCoordinate
end Superfusion

