import Superfusion.GaugeChi.TripleCerts.G0_2
import Superfusion.GaugeChi.TripleCerts.G0_3
import Superfusion.RMod.Constructive.RawSemanticConnectorBridge

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Superfusion
namespace RModCoordinate
namespace RawSemanticSkeletalData

open GaugeChi
open RawSemanticConnector

/-- Raw connector membership at fixed labels (0,6). -/
theorem forward_mem_zero_six : ∀ c : ZMod 8,
    gtOfTNative ℝ realGauge 0 6 c (forwardMatrix 0 6 c) ∈
      gInterSpace ℝ realGauge 0 6 c (parity 0 6 c) :=
  zmod8Rec
    (memOfAlignedCoeff TripleCerts.G0_2.gtOfT0_6_0_mem_gInterSpace (by decide)
      TripleCerts.G0_2.TL0_6_0 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G0_2.gtOfT0_6_1_mem_gInterSpace (by decide)
      TripleCerts.G0_2.TL0_6_1 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G0_2.gtOfT0_6_2_mem_gInterSpace (by decide)
      TripleCerts.G0_2.TL0_6_2 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G0_3.gtOfT0_6_3_mem_gInterSpace (by decide)
      TripleCerts.G0_3.TL0_6_3 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G0_3.gtOfT0_6_4_mem_gInterSpace (by decide)
      TripleCerts.G0_3.TL0_6_4 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G0_3.gtOfT0_6_5_mem_gInterSpace (by decide)
      TripleCerts.G0_3.TL0_6_5 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G0_3.gtOfT0_6_6_mem_gInterSpace (by decide)
      TripleCerts.G0_3.TL0_6_6 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G0_3.gtOfT0_6_7_mem_gInterSpace (by decide)
      TripleCerts.G0_3.TL0_6_7 (by rfl) (by rfl))

end RawSemanticSkeletalData
end RModCoordinate
end Superfusion

