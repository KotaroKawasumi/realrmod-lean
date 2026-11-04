import Superfusion.RMod.Constructive.RawSemanticConnectorMemA3B0
import Superfusion.RMod.Constructive.RawSemanticConnectorMemA3B1
import Superfusion.RMod.Constructive.RawSemanticConnectorMemA3B2
import Superfusion.RMod.Constructive.RawSemanticConnectorMemA3B3
import Superfusion.RMod.Constructive.RawSemanticConnectorMemA3B4
import Superfusion.RMod.Constructive.RawSemanticConnectorMemA3B5
import Superfusion.RMod.Constructive.RawSemanticConnectorMemA3B6
import Superfusion.RMod.Constructive.RawSemanticConnectorMemA3B7

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Superfusion
namespace RModCoordinate
namespace RawSemanticSkeletalData

open GaugeChi
open RawSemanticConnector

/-- Raw connector membership at first label 3. -/
theorem forward_mem_three (b c : ZMod 8) :
    gtOfTNative ℝ realGauge 3 b c (forwardMatrix 3 b c) ∈
      gInterSpace ℝ realGauge 3 b c (parity 3 b c) := by
  fin_cases b
  · exact forward_mem_three_zero c
  · exact forward_mem_three_one c
  · exact forward_mem_three_two c
  · exact forward_mem_three_three c
  · exact forward_mem_three_four c
  · exact forward_mem_three_five c
  · exact forward_mem_three_six c
  · exact forward_mem_three_seven c

end RawSemanticSkeletalData
end RModCoordinate
end Superfusion
