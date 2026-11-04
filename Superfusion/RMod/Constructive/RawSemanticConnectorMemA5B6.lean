import Superfusion.GaugeChi.TripleCerts.G5_12
import Superfusion.GaugeChi.TripleCerts.G5_13
import Superfusion.GaugeChi.TripleCerts.G5_19
import Superfusion.GaugeChi.TripleCerts.G5_20
import Superfusion.RMod.Constructive.RawSemanticConnectorBridge

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Superfusion
namespace RModCoordinate
namespace RawSemanticSkeletalData

open GaugeChi
open RawSemanticConnector

/-- Raw connector membership at fixed labels (5,6). -/
theorem forward_mem_five_six : ∀ c : ZMod 8,
    gtOfTNative ℝ realGauge 5 6 c (forwardMatrix 5 6 c) ∈
      gInterSpace ℝ realGauge 5 6 c (parity 5 6 c) :=
  zmod8Rec
    (memOfAlignedCoeff TripleCerts.G5_19.gtOfT5_6_0_mem_gInterSpace (by decide)
      TripleCerts.G5_19.TL5_6_0 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G5_19.gtOfT5_6_1_mem_gInterSpace (by decide)
      TripleCerts.G5_19.TL5_6_1 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G5_20.gtOfT5_6_2_mem_gInterSpace (by decide)
      TripleCerts.G5_20.TL5_6_2 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G5_12.gtOfT5_6_3_mem_gInterSpace (by decide)
      TripleCerts.G5_12.TL5_6_3 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G5_20.gtOfT5_6_4_mem_gInterSpace (by decide)
      TripleCerts.G5_20.TL5_6_4 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G5_13.gtOfT5_6_5_mem_gInterSpace (by decide)
      TripleCerts.G5_13.TL5_6_5 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G5_20.gtOfT5_6_6_mem_gInterSpace (by decide)
      TripleCerts.G5_20.TL5_6_6 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G5_20.gtOfT5_6_7_mem_gInterSpace (by decide)
      TripleCerts.G5_20.TL5_6_7 (by rfl) (by rfl))

end RawSemanticSkeletalData
end RModCoordinate
end Superfusion

