import Superfusion.GaugeChi.TripleCerts.G2_5
import Superfusion.RMod.Constructive.RawSemanticConnectorBridge

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Superfusion
namespace RModCoordinate
namespace RawSemanticSkeletalData

open GaugeChi
open RawSemanticConnector

/-- Raw connector membership at fixed labels (2,0). -/
theorem forward_mem_two_zero : ∀ c : ZMod 8,
    gtOfTNative ℝ realGauge 2 0 c (forwardMatrix 2 0 c) ∈
      gInterSpace ℝ realGauge 2 0 c (parity 2 0 c) :=
  zmod8Rec
    (memOfAlignedCoeff TripleCerts.G2_5.gtOfT2_0_0_mem_gInterSpace (by decide)
      TripleCerts.G2_5.TL2_0_0 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G2_5.gtOfT2_0_1_mem_gInterSpace (by decide)
      TripleCerts.G2_5.TL2_0_1 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G2_5.gtOfT2_0_2_mem_gInterSpace (by decide)
      TripleCerts.G2_5.TL2_0_2 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G2_5.gtOfT2_0_3_mem_gInterSpace (by decide)
      TripleCerts.G2_5.TL2_0_3 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G2_5.gtOfT2_0_4_mem_gInterSpace (by decide)
      TripleCerts.G2_5.TL2_0_4 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G2_5.gtOfT2_0_5_mem_gInterSpace (by decide)
      TripleCerts.G2_5.TL2_0_5 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G2_5.gtOfT2_0_6_mem_gInterSpace (by decide)
      TripleCerts.G2_5.TL2_0_6 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G2_5.gtOfT2_0_7_mem_gInterSpace (by decide)
      TripleCerts.G2_5.TL2_0_7 (by rfl) (by rfl))

end RawSemanticSkeletalData
end RModCoordinate
end Superfusion

