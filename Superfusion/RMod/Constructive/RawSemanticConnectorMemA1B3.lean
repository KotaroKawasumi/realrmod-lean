import Superfusion.GaugeChi.TripleCerts.BatchMedium
import Superfusion.GaugeChi.TripleCerts.G1_1
import Superfusion.GaugeChi.TripleCerts.G1_2
import Superfusion.RMod.Constructive.RawSemanticConnectorBridge

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Superfusion
namespace RModCoordinate
namespace RawSemanticSkeletalData

open GaugeChi
open RawSemanticConnector

/-- Raw connector membership at fixed labels (1,3). -/
theorem forward_mem_one_three : ∀ c : ZMod 8,
    gtOfTNative ℝ realGauge 1 3 c (forwardMatrix 1 3 c) ∈
      gInterSpace ℝ realGauge 1 3 c (parity 1 3 c) :=
  zmod8Rec
    (memOfAlignedCoeff TripleCerts.G1_1.gtOfT1_3_0_mem_gInterSpace (by decide)
      TripleCerts.G1_1.TL1_3_0 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G1_1.gtOfT1_3_1_mem_gInterSpace (by decide)
      TripleCerts.G1_1.TL1_3_1 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G1_1.gtOfT1_3_2_mem_gInterSpace (by decide)
      TripleCerts.G1_1.TL1_3_2 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G1_2.gtOfT1_3_3_mem_gInterSpace (by decide)
      TripleCerts.G1_2.TL1_3_3 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G1_2.gtOfT1_3_4_mem_gInterSpace (by decide)
      TripleCerts.G1_2.TL1_3_4 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G1_2.gtOfT1_3_5_mem_gInterSpace (by decide)
      TripleCerts.G1_2.TL1_3_5 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.BatchMedium.gtOfT1_3_6_mem_gInterSpace (by decide)
      TripleCerts.BatchMedium.TL1_3_6 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G1_2.gtOfT1_3_7_mem_gInterSpace (by decide)
      TripleCerts.G1_2.TL1_3_7 (by rfl) (by rfl))

end RawSemanticSkeletalData
end RModCoordinate
end Superfusion

