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

/-- Raw connector membership at fixed labels (1,6). -/
theorem forward_mem_one_six : ∀ c : ZMod 8,
    gtOfTNative ℝ realGauge 1 6 c (forwardMatrix 1 6 c) ∈
      gInterSpace ℝ realGauge 1 6 c (parity 1 6 c) :=
  zmod8Rec
    (memOfAlignedCoeff TripleCerts.G1_4.gtOfT1_6_0_mem_gInterSpace (by decide)
      TripleCerts.G1_4.TL1_6_0 (by rfl) (by rfl))
    (memOfAlignedRaw gtOfT161_mem_gInterSpace (by decide) (by rfl))
    (memOfAlignedCoeff TripleCerts.G1_4.gtOfT1_6_2_mem_gInterSpace (by decide)
      TripleCerts.G1_4.TL1_6_2 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G1_4.gtOfT1_6_3_mem_gInterSpace (by decide)
      TripleCerts.G1_4.TL1_6_3 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G1_4.gtOfT1_6_4_mem_gInterSpace (by decide)
      TripleCerts.G1_4.TL1_6_4 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G1_4.gtOfT1_6_5_mem_gInterSpace (by decide)
      TripleCerts.G1_4.TL1_6_5 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G1_4.gtOfT1_6_6_mem_gInterSpace (by decide)
      TripleCerts.G1_4.TL1_6_6 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G1_4.gtOfT1_6_7_mem_gInterSpace (by decide)
      TripleCerts.G1_4.TL1_6_7 (by rfl) (by rfl))

end RawSemanticSkeletalData
end RModCoordinate
end Superfusion

