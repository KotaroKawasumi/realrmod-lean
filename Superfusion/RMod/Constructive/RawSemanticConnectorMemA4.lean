import Superfusion.RMod.Constructive.RawSemanticConnectorMemA4B0
import Superfusion.RMod.Constructive.RawSemanticConnectorMemA4B1
import Superfusion.RMod.Constructive.RawSemanticConnectorMemA4B2
import Superfusion.RMod.Constructive.RawSemanticConnectorMemA4B3
import Superfusion.RMod.Constructive.RawSemanticConnectorMemA4B4
import Superfusion.RMod.Constructive.RawSemanticConnectorMemA4B5
import Superfusion.RMod.Constructive.RawSemanticConnectorMemA4B6
import Superfusion.RMod.Constructive.RawSemanticConnectorMemA4B7

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Superfusion
namespace RModCoordinate
namespace RawSemanticSkeletalData

open GaugeChi
open RawSemanticConnector

/-- Raw connector membership at first label 4. -/
theorem forward_mem_four (b c : ZMod 8) :
    gtOfTNative ℝ realGauge 4 b c (forwardMatrix 4 b c) ∈
      gInterSpace ℝ realGauge 4 b c (parity 4 b c) := by
  fin_cases b
  · exact forward_mem_four_zero c
  · exact forward_mem_four_one c
  · exact forward_mem_four_two c
  · exact forward_mem_four_three c
  · exact forward_mem_four_four c
  · exact forward_mem_four_five c
  · exact forward_mem_four_six c
  · exact forward_mem_four_seven c

end RawSemanticSkeletalData
end RModCoordinate
end Superfusion
