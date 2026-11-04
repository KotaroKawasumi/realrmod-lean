import Superfusion.RMod.Constructive.RawSemanticConnectorMemA2B0
import Superfusion.RMod.Constructive.RawSemanticConnectorMemA2B1
import Superfusion.RMod.Constructive.RawSemanticConnectorMemA2B2
import Superfusion.RMod.Constructive.RawSemanticConnectorMemA2B3
import Superfusion.RMod.Constructive.RawSemanticConnectorMemA2B4
import Superfusion.RMod.Constructive.RawSemanticConnectorMemA2B5
import Superfusion.RMod.Constructive.RawSemanticConnectorMemA2B6
import Superfusion.RMod.Constructive.RawSemanticConnectorMemA2B7

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Superfusion
namespace RModCoordinate
namespace RawSemanticSkeletalData

open GaugeChi
open RawSemanticConnector

/-- Raw connector membership at first label 2. -/
theorem forward_mem_two (b c : ZMod 8) :
    gtOfTNative ℝ realGauge 2 b c (forwardMatrix 2 b c) ∈
      gInterSpace ℝ realGauge 2 b c (parity 2 b c) := by
  fin_cases b
  · exact forward_mem_two_zero c
  · exact forward_mem_two_one c
  · exact forward_mem_two_two c
  · exact forward_mem_two_three c
  · exact forward_mem_two_four c
  · exact forward_mem_two_five c
  · exact forward_mem_two_six c
  · exact forward_mem_two_seven c

end RawSemanticSkeletalData
end RModCoordinate
end Superfusion
