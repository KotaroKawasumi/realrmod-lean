import Superfusion.RMod.Constructive.RawSemanticConnectorMemA1B0
import Superfusion.RMod.Constructive.RawSemanticConnectorMemA1B1
import Superfusion.RMod.Constructive.RawSemanticConnectorMemA1B2
import Superfusion.RMod.Constructive.RawSemanticConnectorMemA1B3
import Superfusion.RMod.Constructive.RawSemanticConnectorMemA1B4
import Superfusion.RMod.Constructive.RawSemanticConnectorMemA1B5
import Superfusion.RMod.Constructive.RawSemanticConnectorMemA1B6
import Superfusion.RMod.Constructive.RawSemanticConnectorMemA1B7

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Superfusion
namespace RModCoordinate
namespace RawSemanticSkeletalData

open GaugeChi
open RawSemanticConnector

/-- Raw connector membership at first label 1. -/
theorem forward_mem_one (b c : ZMod 8) :
    gtOfTNative ℝ realGauge 1 b c (forwardMatrix 1 b c) ∈
      gInterSpace ℝ realGauge 1 b c (parity 1 b c) := by
  fin_cases b
  · exact forward_mem_one_zero c
  · exact forward_mem_one_one c
  · exact forward_mem_one_two c
  · exact forward_mem_one_three c
  · exact forward_mem_one_four c
  · exact forward_mem_one_five c
  · exact forward_mem_one_six c
  · exact forward_mem_one_seven c

end RawSemanticSkeletalData
end RModCoordinate
end Superfusion
