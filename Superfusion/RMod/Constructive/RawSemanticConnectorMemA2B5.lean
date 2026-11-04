import Superfusion.GaugeChi.TripleCerts.G2_10
import Superfusion.GaugeChi.TripleCerts.G2_3
import Superfusion.GaugeChi.TripleCerts.G2_4
import Superfusion.GaugeChi.TripleCerts.G2_9
import Superfusion.RMod.Constructive.RawSemanticConnectorBridge

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Superfusion
namespace RModCoordinate
namespace RawSemanticSkeletalData

open GaugeChi
open RawSemanticConnector

/-- Raw connector membership at fixed labels (2,5). -/
theorem forward_mem_two_five : ∀ c : ZMod 8,
    gtOfTNative ℝ realGauge 2 5 c (forwardMatrix 2 5 c) ∈
      gInterSpace ℝ realGauge 2 5 c (parity 2 5 c) :=
  zmod8Rec
    (memOfAlignedCoeff TripleCerts.G2_9.gtOfT2_5_0_mem_gInterSpace (by decide)
      TripleCerts.G2_9.TL2_5_0 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G2_9.gtOfT2_5_1_mem_gInterSpace (by decide)
      TripleCerts.G2_9.TL2_5_1 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G2_9.gtOfT2_5_2_mem_gInterSpace (by decide)
      TripleCerts.G2_9.TL2_5_2 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G2_3.gtOfT2_5_3_mem_gInterSpace (by decide)
      TripleCerts.G2_3.TL2_5_3 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G2_10.gtOfT2_5_4_mem_gInterSpace (by decide)
      TripleCerts.G2_10.TL2_5_4 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G2_4.gtOfT2_5_5_mem_gInterSpace (by decide)
      TripleCerts.G2_4.TL2_5_5 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G2_10.gtOfT2_5_6_mem_gInterSpace (by decide)
      TripleCerts.G2_10.TL2_5_6 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G2_10.gtOfT2_5_7_mem_gInterSpace (by decide)
      TripleCerts.G2_10.TL2_5_7 (by rfl) (by rfl))

end RawSemanticSkeletalData
end RModCoordinate
end Superfusion

