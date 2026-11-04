import Superfusion.RMod.Constructive.RawSemanticConnectorMemA5B0
import Superfusion.RMod.Constructive.RawSemanticConnectorMemA5B1
import Superfusion.RMod.Constructive.RawSemanticConnectorMemA5B2
import Superfusion.RMod.Constructive.RawSemanticConnectorMemA5B3
import Superfusion.RMod.Constructive.RawSemanticConnectorMemA5B4
import Superfusion.RMod.Constructive.RawSemanticConnectorMemA5B5
import Superfusion.RMod.Constructive.RawSemanticConnectorMemA5B6
import Superfusion.RMod.Constructive.RawSemanticConnectorMemA5B7

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Superfusion
namespace RModCoordinate
namespace RawSemanticSkeletalData

open GaugeChi
open RawSemanticConnector

/-- Raw connector membership at first label 5. -/
theorem forward_mem_five (b c : ZMod 8) :
    gtOfTNative ℝ realGauge 5 b c (forwardMatrix 5 b c) ∈
      gInterSpace ℝ realGauge 5 b c (parity 5 b c) := by
  fin_cases b
  · exact forward_mem_five_zero c
  · exact forward_mem_five_one c
  · exact forward_mem_five_two c
  · exact forward_mem_five_three c
  · exact forward_mem_five_four c
  · exact forward_mem_five_five c
  · exact forward_mem_five_six c
  · exact forward_mem_five_seven c

end RawSemanticSkeletalData
end RModCoordinate
end Superfusion
