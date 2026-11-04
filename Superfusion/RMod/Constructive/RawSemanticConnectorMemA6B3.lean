import Superfusion.GaugeChi.TripleCerts.G6_1
import Superfusion.GaugeChi.TripleCerts.G6_2
import Superfusion.GaugeChi.TripleCerts.G6_7
import Superfusion.GaugeChi.TripleCerts.G6_8
import Superfusion.RMod.Constructive.RawSemanticConnectorBridge

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Superfusion
namespace RModCoordinate
namespace RawSemanticSkeletalData

open GaugeChi
open RawSemanticConnector

/-- Raw connector membership at fixed labels (6,3). -/
theorem forward_mem_six_three : ∀ c : ZMod 8,
    gtOfTNative ℝ realGauge 6 3 c (forwardMatrix 6 3 c) ∈
      gInterSpace ℝ realGauge 6 3 c (parity 6 3 c) :=
  zmod8Rec
    (memOfAlignedCoeff TripleCerts.G6_7.gtOfT6_3_0_mem_gInterSpace (by decide)
      TripleCerts.G6_7.TL6_3_0 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G6_7.gtOfT6_3_1_mem_gInterSpace (by decide)
      TripleCerts.G6_7.TL6_3_1 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G6_7.gtOfT6_3_2_mem_gInterSpace (by decide)
      TripleCerts.G6_7.TL6_3_2 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G6_1.gtOfT6_3_3_mem_gInterSpace (by decide)
      TripleCerts.G6_1.TL6_3_3 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G6_7.gtOfT6_3_4_mem_gInterSpace (by decide)
      TripleCerts.G6_7.TL6_3_4 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G6_2.gtOfT6_3_5_mem_gInterSpace (by decide)
      TripleCerts.G6_2.TL6_3_5 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G6_8.gtOfT6_3_6_mem_gInterSpace (by decide)
      TripleCerts.G6_8.TL6_3_6 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G6_8.gtOfT6_3_7_mem_gInterSpace (by decide)
      TripleCerts.G6_8.TL6_3_7 (by rfl) (by rfl))

end RawSemanticSkeletalData
end RModCoordinate
end Superfusion

