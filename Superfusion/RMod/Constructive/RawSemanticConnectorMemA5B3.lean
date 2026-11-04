import Superfusion.GaugeChi.TripleCerts.BatchHeavy
import Superfusion.GaugeChi.TripleCerts.G5_17
import Superfusion.GaugeChi.TripleCerts.G5_3
import Superfusion.GaugeChi.TripleCerts.G5_4
import Superfusion.GaugeChi.TripleCerts.G5_5
import Superfusion.RMod.Constructive.RawSemanticConnectorBridge

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Superfusion
namespace RModCoordinate
namespace RawSemanticSkeletalData

open GaugeChi
open RawSemanticConnector

/-- Raw connector membership at fixed labels (5,3). -/
theorem forward_mem_five_three : ∀ c : ZMod 8,
    gtOfTNative ℝ realGauge 5 3 c (forwardMatrix 5 3 c) ∈
      gInterSpace ℝ realGauge 5 3 c (parity 5 3 c) :=
  zmod8Rec
    (memOfAlignedCoeff TripleCerts.G5_17.gtOfT5_3_0_mem_gInterSpace (by decide)
      TripleCerts.G5_17.TL5_3_0 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G5_17.gtOfT5_3_1_mem_gInterSpace (by decide)
      TripleCerts.G5_17.TL5_3_1 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G5_3.gtOfT5_3_2_mem_gInterSpace (by decide)
      TripleCerts.G5_3.TL5_3_2 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.BatchHeavy.gtOfT5_3_3_mem_gInterSpace (by decide)
      TripleCerts.BatchHeavy.TL5_3_3 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G5_4.gtOfT5_3_4_mem_gInterSpace (by decide)
      TripleCerts.G5_4.TL5_3_4 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.BatchHeavy.gtOfT5_3_5_mem_gInterSpace (by decide)
      TripleCerts.BatchHeavy.TL5_3_5 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G5_5.gtOfT5_3_6_mem_gInterSpace (by decide)
      TripleCerts.G5_5.TL5_3_6 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G5_17.gtOfT5_3_7_mem_gInterSpace (by decide)
      TripleCerts.G5_17.TL5_3_7 (by rfl) (by rfl))

end RawSemanticSkeletalData
end RModCoordinate
end Superfusion

