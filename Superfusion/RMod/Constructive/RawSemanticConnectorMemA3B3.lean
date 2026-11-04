import Superfusion.GaugeChi.TripleCerts.BatchHeavy
import Superfusion.GaugeChi.TripleCerts.G3_17
import Superfusion.GaugeChi.TripleCerts.G3_3
import Superfusion.GaugeChi.TripleCerts.G3_4
import Superfusion.GaugeChi.TripleCerts.G3_5
import Superfusion.GaugeChi.TripleCerts.G3_6
import Superfusion.RMod.Constructive.RawSemanticConnectorBridge

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Superfusion
namespace RModCoordinate
namespace RawSemanticSkeletalData

open GaugeChi
open RawSemanticConnector

/-- Raw connector membership at fixed labels (3,3). -/
theorem forward_mem_three_three : ∀ c : ZMod 8,
    gtOfTNative ℝ realGauge 3 3 c (forwardMatrix 3 3 c) ∈
      gInterSpace ℝ realGauge 3 3 c (parity 3 3 c) :=
  zmod8Rec
    (memOfAlignedCoeff TripleCerts.G3_17.gtOfT3_3_0_mem_gInterSpace (by decide)
      TripleCerts.G3_17.TL3_3_0 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G3_17.gtOfT3_3_1_mem_gInterSpace (by decide)
      TripleCerts.G3_17.TL3_3_1 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G3_3.gtOfT3_3_2_mem_gInterSpace (by decide)
      TripleCerts.G3_3.TL3_3_2 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G3_4.gtOfT3_3_3_mem_gInterSpace (by decide)
      TripleCerts.G3_4.TL3_3_3 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G3_5.gtOfT3_3_4_mem_gInterSpace (by decide)
      TripleCerts.G3_5.TL3_3_4 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.BatchHeavy.gtOfT3_3_5_mem_gInterSpace (by decide)
      TripleCerts.BatchHeavy.TL3_3_5 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G3_6.gtOfT3_3_6_mem_gInterSpace (by decide)
      TripleCerts.G3_6.TL3_3_6 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G3_17.gtOfT3_3_7_mem_gInterSpace (by decide)
      TripleCerts.G3_17.TL3_3_7 (by rfl) (by rfl))

end RawSemanticSkeletalData
end RModCoordinate
end Superfusion

