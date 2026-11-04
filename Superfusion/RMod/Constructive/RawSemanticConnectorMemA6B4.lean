import Superfusion.GaugeChi.TripleCerts.Exceptional
import Superfusion.GaugeChi.TripleCerts.G6_8
import Superfusion.GaugeChi.TripleCerts.G6_9
import Superfusion.RMod.Constructive.RawSemanticConnectorBridge

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Superfusion
namespace RModCoordinate
namespace RawSemanticSkeletalData

open GaugeChi
open RawSemanticConnector

/-- Raw connector membership at fixed labels (6,4). -/
theorem forward_mem_six_four : ∀ c : ZMod 8,
    gtOfTNative ℝ realGauge 6 4 c (forwardMatrix 6 4 c) ∈
      gInterSpace ℝ realGauge 6 4 c (parity 6 4 c) :=
  zmod8Rec
    (memOfAlignedCoeff TripleCerts.G6_8.gtOfT6_4_0_mem_gInterSpace (by decide)
      TripleCerts.G6_8.TL6_4_0 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G6_8.gtOfT6_4_1_mem_gInterSpace (by decide)
      TripleCerts.G6_8.TL6_4_1 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G6_8.gtOfT6_4_2_mem_gInterSpace (by decide)
      TripleCerts.G6_8.TL6_4_2 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G6_8.gtOfT6_4_3_mem_gInterSpace (by decide)
      TripleCerts.G6_8.TL6_4_3 (by rfl) (by rfl))
    (memOfNativeCoeff TripleCerts.Exceptional.gtOfTNative6_4_4_mem_gInterSpace (by decide)
      TripleCerts.Exceptional.TL6_4_4 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G6_9.gtOfT6_4_5_mem_gInterSpace (by decide)
      TripleCerts.G6_9.TL6_4_5 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G6_9.gtOfT6_4_6_mem_gInterSpace (by decide)
      TripleCerts.G6_9.TL6_4_6 (by rfl) (by rfl))
    (memOfAlignedCoeff TripleCerts.G6_9.gtOfT6_4_7_mem_gInterSpace (by decide)
      TripleCerts.G6_9.TL6_4_7 (by rfl) (by rfl))

end RawSemanticSkeletalData
end RModCoordinate
end Superfusion

