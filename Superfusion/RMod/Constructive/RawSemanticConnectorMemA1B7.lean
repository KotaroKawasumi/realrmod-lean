import Superfusion.GaugeChi.TripleCerts.G1_4
import Superfusion.RMod.Constructive.RawSemanticConnectorBridge

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Superfusion
namespace RModCoordinate
namespace RawSemanticSkeletalData

open GaugeChi
open RawSemanticConnector

/-- Raw connector membership at fixed labels (1,7). -/
theorem forward_mem_one_seven : ∀ c : ZMod 8,
    gtOfTNative ℝ realGauge 1 7 c (forwardMatrix 1 7 c) ∈
      gInterSpace ℝ realGauge 1 7 c (parity 1 7 c) :=
  zmod8Rec
    (memOfAlignedCoeff TripleCerts.G1_4.gtOfT1_7_0_mem_gInterSpace (by decide)
      TripleCerts.G1_4.TL1_7_0 (by rfl) (by rfl))
    (memOfAlignedRaw gtOfT171_mem_gInterSpace (by decide) (by rfl))
    (memOfAlignedCoeff TripleCerts.G1_4.gtOfT1_7_2_mem_gInterSpace (by decide)
      TripleCerts.G1_4.TL1_7_2 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G1_4.gtOfT1_7_3_mem_gInterSpace (by decide)
      TripleCerts.G1_4.TL1_7_3 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G1_4.gtOfT1_7_4_mem_gInterSpace (by decide)
      TripleCerts.G1_4.TL1_7_4 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G1_4.gtOfT1_7_5_mem_gInterSpace (by decide)
      TripleCerts.G1_4.TL1_7_5 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G1_4.gtOfT1_7_6_mem_gInterSpace (by decide)
      TripleCerts.G1_4.TL1_7_6 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G1_4.gtOfT1_7_7_mem_gInterSpace (by decide)
      TripleCerts.G1_4.TL1_7_7 (by rfl) (by rfl))

end RawSemanticSkeletalData
end RModCoordinate
end Superfusion

