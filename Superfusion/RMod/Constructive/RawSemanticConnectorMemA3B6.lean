import Superfusion.GaugeChi.TripleCerts.G3_12
import Superfusion.GaugeChi.TripleCerts.G3_13
import Superfusion.GaugeChi.TripleCerts.G3_19
import Superfusion.GaugeChi.TripleCerts.G3_20
import Superfusion.RMod.Constructive.RawSemanticConnectorBridge

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Superfusion
namespace RModCoordinate
namespace RawSemanticSkeletalData

open GaugeChi
open RawSemanticConnector

/-- Raw connector membership at fixed labels (3,6). -/
theorem forward_mem_three_six : ∀ c : ZMod 8,
    gtOfTNative ℝ realGauge 3 6 c (forwardMatrix 3 6 c) ∈
      gInterSpace ℝ realGauge 3 6 c (parity 3 6 c) :=
  zmod8Rec
    (memOfAlignedCoeff TripleCerts.G3_19.gtOfT3_6_0_mem_gInterSpace (by decide)
      TripleCerts.G3_19.TL3_6_0 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G3_19.gtOfT3_6_1_mem_gInterSpace (by decide)
      TripleCerts.G3_19.TL3_6_1 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G3_20.gtOfT3_6_2_mem_gInterSpace (by decide)
      TripleCerts.G3_20.TL3_6_2 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G3_12.gtOfT3_6_3_mem_gInterSpace (by decide)
      TripleCerts.G3_12.TL3_6_3 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G3_20.gtOfT3_6_4_mem_gInterSpace (by decide)
      TripleCerts.G3_20.TL3_6_4 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G3_13.gtOfT3_6_5_mem_gInterSpace (by decide)
      TripleCerts.G3_13.TL3_6_5 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G3_20.gtOfT3_6_6_mem_gInterSpace (by decide)
      TripleCerts.G3_20.TL3_6_6 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G3_20.gtOfT3_6_7_mem_gInterSpace (by decide)
      TripleCerts.G3_20.TL3_6_7 (by rfl) (by rfl))

end RawSemanticSkeletalData
end RModCoordinate
end Superfusion

