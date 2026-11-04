import Superfusion.RMod.Constructive.RawSemanticConnectorMemA0B0
import Superfusion.RMod.Constructive.RawSemanticConnectorMemA0B1
import Superfusion.RMod.Constructive.RawSemanticConnectorMemA0B2
import Superfusion.RMod.Constructive.RawSemanticConnectorMemA0B3
import Superfusion.RMod.Constructive.RawSemanticConnectorMemA0B4
import Superfusion.RMod.Constructive.RawSemanticConnectorMemA0B5
import Superfusion.RMod.Constructive.RawSemanticConnectorMemA0B6
import Superfusion.RMod.Constructive.RawSemanticConnectorMemA0B7

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Superfusion
namespace RModCoordinate
namespace RawSemanticSkeletalData

open GaugeChi
open RawSemanticConnector

/-- Raw connector membership at first label 0. -/
theorem forward_mem_zero (b c : ZMod 8) :
    gtOfTNative ℝ realGauge 0 b c (forwardMatrix 0 b c) ∈
      gInterSpace ℝ realGauge 0 b c (parity 0 b c) := by
  fin_cases b
  · exact forward_mem_zero_zero c
  · exact forward_mem_zero_one c
  · exact forward_mem_zero_two c
  · exact forward_mem_zero_three c
  · exact forward_mem_zero_four c
  · exact forward_mem_zero_five c
  · exact forward_mem_zero_six c
  · exact forward_mem_zero_seven c

end RawSemanticSkeletalData
end RModCoordinate
end Superfusion
