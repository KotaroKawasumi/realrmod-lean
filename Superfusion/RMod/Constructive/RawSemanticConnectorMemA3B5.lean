import Superfusion.GaugeChi.TripleCerts.BatchHeavy
import Superfusion.GaugeChi.TripleCerts.G3_10
import Superfusion.GaugeChi.TripleCerts.G3_11
import Superfusion.GaugeChi.TripleCerts.G3_18
import Superfusion.GaugeChi.TripleCerts.G3_19
import Superfusion.GaugeChi.TripleCerts.G3_9
import Superfusion.RMod.Constructive.RawSemanticConnectorBridge

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Superfusion
namespace RModCoordinate
namespace RawSemanticSkeletalData

open GaugeChi
open RawSemanticConnector

/-- Raw connector membership at fixed labels (3,5). -/
theorem forward_mem_three_five : ∀ c : ZMod 8,
    gtOfTNative ℝ realGauge 3 5 c (forwardMatrix 3 5 c) ∈
      gInterSpace ℝ realGauge 3 5 c (parity 3 5 c) :=
  zmod8Rec
    (memOfAlignedCoeff TripleCerts.G3_18.gtOfT3_5_0_mem_gInterSpace (by decide)
      TripleCerts.G3_18.TL3_5_0 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G3_19.gtOfT3_5_1_mem_gInterSpace (by decide)
      TripleCerts.G3_19.TL3_5_1 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G3_9.gtOfT3_5_2_mem_gInterSpace (by decide)
      TripleCerts.G3_9.TL3_5_2 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.BatchHeavy.gtOfT3_5_3_mem_gInterSpace (by decide)
      TripleCerts.BatchHeavy.TL3_5_3 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G3_10.gtOfT3_5_4_mem_gInterSpace (by decide)
      TripleCerts.G3_10.TL3_5_4 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.BatchHeavy.gtOfT3_5_5_mem_gInterSpace (by decide)
      TripleCerts.BatchHeavy.TL3_5_5 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G3_11.gtOfT3_5_6_mem_gInterSpace (by decide)
      TripleCerts.G3_11.TL3_5_6 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G3_19.gtOfT3_5_7_mem_gInterSpace (by decide)
      TripleCerts.G3_19.TL3_5_7 (by rfl) (by rfl))

end RawSemanticSkeletalData
end RModCoordinate
end Superfusion

