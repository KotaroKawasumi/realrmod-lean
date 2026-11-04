import Superfusion.RMod.Constructive.RawSemanticConnectorMemA6B0
import Superfusion.RMod.Constructive.RawSemanticConnectorMemA6B1
import Superfusion.RMod.Constructive.RawSemanticConnectorMemA6B2
import Superfusion.RMod.Constructive.RawSemanticConnectorMemA6B3
import Superfusion.RMod.Constructive.RawSemanticConnectorMemA6B4
import Superfusion.RMod.Constructive.RawSemanticConnectorMemA6B5
import Superfusion.RMod.Constructive.RawSemanticConnectorMemA6B6
import Superfusion.RMod.Constructive.RawSemanticConnectorMemA6B7

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Superfusion
namespace RModCoordinate
namespace RawSemanticSkeletalData

open GaugeChi
open RawSemanticConnector

/-- Raw connector membership at first label 6. -/
theorem forward_mem_six (b c : ZMod 8) :
    gtOfTNative ℝ realGauge 6 b c (forwardMatrix 6 b c) ∈
      gInterSpace ℝ realGauge 6 b c (parity 6 b c) := by
  fin_cases b
  · exact forward_mem_six_zero c
  · exact forward_mem_six_one c
  · exact forward_mem_six_two c
  · exact forward_mem_six_three c
  · exact forward_mem_six_four c
  · exact forward_mem_six_five c
  · exact forward_mem_six_six c
  · exact forward_mem_six_seven c

end RawSemanticSkeletalData
end RModCoordinate
end Superfusion
