import Superfusion.RMod.Constructive.ConnectorTableInverseCertificate

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Superfusion
namespace RModCoordinate
namespace ConnectorTableLaws

open RMod.ConstructiveConnectorTable

theorem inverseCertificate_3_3_6 :
    (checkForwardInverseNat 3 3 6 && checkInverseForwardNat 3 3 6) = true := by
  decide +kernel

end ConnectorTableLaws
end RModCoordinate
end Superfusion
