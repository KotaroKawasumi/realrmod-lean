import Superfusion.RMod.Constructive.RawSemanticConnectorMemA7B0
import Superfusion.RMod.Constructive.RawSemanticConnectorMemA7B1
import Superfusion.RMod.Constructive.RawSemanticConnectorMemA7B2
import Superfusion.RMod.Constructive.RawSemanticConnectorMemA7B3
import Superfusion.RMod.Constructive.RawSemanticConnectorMemA7B4
import Superfusion.RMod.Constructive.RawSemanticConnectorMemA7B5
import Superfusion.RMod.Constructive.RawSemanticConnectorMemA7B6
import Superfusion.RMod.Constructive.RawSemanticConnectorMemA7B7

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Superfusion
namespace RModCoordinate
namespace RawSemanticSkeletalData

open GaugeChi
open RawSemanticConnector

/-- Raw connector membership at first label 7. -/
theorem forward_mem_seven (b c : ZMod 8) :
    gtOfTNative ℝ realGauge 7 b c (forwardMatrix 7 b c) ∈
      gInterSpace ℝ realGauge 7 b c (parity 7 b c) := by
  fin_cases b
  · exact forward_mem_seven_zero c
  · exact forward_mem_seven_one c
  · exact forward_mem_seven_two c
  · exact forward_mem_seven_three c
  · exact forward_mem_seven_four c
  · exact forward_mem_seven_five c
  · exact forward_mem_seven_six c
  · exact forward_mem_seven_seven c

end RawSemanticSkeletalData
end RModCoordinate
end Superfusion
