import Superfusion.GaugeChi.TripleCerts.BatchMedium
import Superfusion.GaugeChi.TripleCerts.G1_1
import Superfusion.RMod.Constructive.RawSemanticConnectorBridge

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Superfusion
namespace RModCoordinate
namespace RawSemanticSkeletalData

open GaugeChi
open RawSemanticConnector

/-- Raw connector membership at fixed labels (1,2). -/
theorem forward_mem_one_two : ∀ c : ZMod 8,
    gtOfTNative ℝ realGauge 1 2 c (forwardMatrix 1 2 c) ∈
      gInterSpace ℝ realGauge 1 2 c (parity 1 2 c) :=
  zmod8Rec
    (memOfAlignedCoeff TripleCerts.G1_1.gtOfT1_2_0_mem_gInterSpace (by decide)
      TripleCerts.G1_1.TL1_2_0 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G1_1.gtOfT1_2_1_mem_gInterSpace (by decide)
      TripleCerts.G1_1.TL1_2_1 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G1_1.gtOfT1_2_2_mem_gInterSpace (by decide)
      TripleCerts.G1_1.TL1_2_2 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.BatchMedium.gtOfT1_2_3_mem_gInterSpace (by decide)
      TripleCerts.BatchMedium.TL1_2_3 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.BatchMedium.gtOfT1_2_4_mem_gInterSpace (by decide)
      TripleCerts.BatchMedium.TL1_2_4 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G1_1.gtOfT1_2_5_mem_gInterSpace (by decide)
      TripleCerts.G1_1.TL1_2_5 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G1_1.gtOfT1_2_6_mem_gInterSpace (by decide)
      TripleCerts.G1_1.TL1_2_6 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G1_1.gtOfT1_2_7_mem_gInterSpace (by decide)
      TripleCerts.G1_1.TL1_2_7 (by rfl) (by rfl))

end RawSemanticSkeletalData
end RModCoordinate
end Superfusion

