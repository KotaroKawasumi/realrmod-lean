import Superfusion.GaugeChi.TripleCerts.BatchHeavy
import Superfusion.GaugeChi.TripleCerts.G5_10
import Superfusion.GaugeChi.TripleCerts.G5_11
import Superfusion.GaugeChi.TripleCerts.G5_18
import Superfusion.GaugeChi.TripleCerts.G5_19
import Superfusion.GaugeChi.TripleCerts.G5_8
import Superfusion.GaugeChi.TripleCerts.G5_9
import Superfusion.RMod.Constructive.RawSemanticConnectorBridge

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Superfusion
namespace RModCoordinate
namespace RawSemanticSkeletalData

open GaugeChi
open RawSemanticConnector

/-- Raw connector membership at fixed labels (5,5). -/
theorem forward_mem_five_five : ∀ c : ZMod 8,
    gtOfTNative ℝ realGauge 5 5 c (forwardMatrix 5 5 c) ∈
      gInterSpace ℝ realGauge 5 5 c (parity 5 5 c) :=
  zmod8Rec
    (memOfAlignedCoeff TripleCerts.G5_18.gtOfT5_5_0_mem_gInterSpace (by decide)
      TripleCerts.G5_18.TL5_5_0 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G5_19.gtOfT5_5_1_mem_gInterSpace (by decide)
      TripleCerts.G5_19.TL5_5_1 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G5_8.gtOfT5_5_2_mem_gInterSpace (by decide)
      TripleCerts.G5_8.TL5_5_2 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.BatchHeavy.gtOfT5_5_3_mem_gInterSpace (by decide)
      TripleCerts.BatchHeavy.TL5_5_3 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G5_9.gtOfT5_5_4_mem_gInterSpace (by decide)
      TripleCerts.G5_9.TL5_5_4 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G5_10.gtOfT5_5_5_mem_gInterSpace (by decide)
      TripleCerts.G5_10.TL5_5_5 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G5_11.gtOfT5_5_6_mem_gInterSpace (by decide)
      TripleCerts.G5_11.TL5_5_6 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G5_19.gtOfT5_5_7_mem_gInterSpace (by decide)
      TripleCerts.G5_19.TL5_5_7 (by rfl) (by rfl))

end RawSemanticSkeletalData
end RModCoordinate
end Superfusion

