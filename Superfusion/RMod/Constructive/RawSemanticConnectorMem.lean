import Superfusion.RMod.Constructive.RawSemanticConnectorMemA0
import Superfusion.RMod.Constructive.RawSemanticConnectorMemA1
import Superfusion.RMod.Constructive.RawSemanticConnectorMemA2
import Superfusion.RMod.Constructive.RawSemanticConnectorMemA3
import Superfusion.RMod.Constructive.RawSemanticConnectorMemA4
import Superfusion.RMod.Constructive.RawSemanticConnectorMemA5
import Superfusion.RMod.Constructive.RawSemanticConnectorMemA6
import Superfusion.RMod.Constructive.RawSemanticConnectorMemA7

/-!
# Uniform membership of the raw forward connector

The 512 existing `TripleCerts` theorems are assembled here into one theorem
for the literal raw forward matrix.  No connector is selected from an
existence statement, and no inverse or shifted normalization is introduced.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Superfusion
namespace RModCoordinate
namespace RawSemanticSkeletalData

open GaugeChi
open RawSemanticConnector

/-- Full semantic intertwining certificate for the frozen raw table. -/
theorem forward_mem (a b c : ZMod 8) :
    gtOfTNative ℝ realGauge a b c (forwardMatrix a b c) ∈
      gInterSpace ℝ realGauge a b c (parity a b c) := by
  fin_cases a
  · exact forward_mem_zero b c
  · exact forward_mem_one b c
  · exact forward_mem_two b c
  · exact forward_mem_three b c
  · exact forward_mem_four b c
  · exact forward_mem_five b c
  · exact forward_mem_six b c
  · exact forward_mem_seven b c

end RawSemanticSkeletalData
end RModCoordinate
end Superfusion
