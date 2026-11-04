import Superfusion.GaugeChi.TripleCerts.G2_10
import Superfusion.GaugeChi.TripleCerts.G2_11
import Superfusion.RMod.Constructive.RawSemanticConnectorBridge

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Superfusion
namespace RModCoordinate
namespace RawSemanticSkeletalData

open GaugeChi
open RawSemanticConnector

/-- Raw connector membership at fixed labels (2,6). -/
theorem forward_mem_two_six : ∀ c : ZMod 8,
    gtOfTNative ℝ realGauge 2 6 c (forwardMatrix 2 6 c) ∈
      gInterSpace ℝ realGauge 2 6 c (parity 2 6 c) :=
  zmod8Rec
    (memOfAlignedCoeff TripleCerts.G2_10.gtOfT2_6_0_mem_gInterSpace (by decide)
      TripleCerts.G2_10.TL2_6_0 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G2_10.gtOfT2_6_1_mem_gInterSpace (by decide)
      TripleCerts.G2_10.TL2_6_1 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G2_10.gtOfT2_6_2_mem_gInterSpace (by decide)
      TripleCerts.G2_10.TL2_6_2 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G2_11.gtOfT2_6_3_mem_gInterSpace (by decide)
      TripleCerts.G2_11.TL2_6_3 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G2_11.gtOfT2_6_4_mem_gInterSpace (by decide)
      TripleCerts.G2_11.TL2_6_4 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G2_11.gtOfT2_6_5_mem_gInterSpace (by decide)
      TripleCerts.G2_11.TL2_6_5 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G2_11.gtOfT2_6_6_mem_gInterSpace (by decide)
      TripleCerts.G2_11.TL2_6_6 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G2_11.gtOfT2_6_7_mem_gInterSpace (by decide)
      TripleCerts.G2_11.TL2_6_7 (by rfl) (by rfl))

end RawSemanticSkeletalData
end RModCoordinate
end Superfusion

