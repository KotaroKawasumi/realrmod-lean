import Superfusion.RMod.Constructive.ConnectorTableInverseCertificate

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Superfusion
namespace RModCoordinate
namespace ConnectorTableLaws

theorem inverseCertificatesForAB_three_zero :
    inverseCertificatesForAB 3 0 = true := by
  decide +kernel

end ConnectorTableLaws
end RModCoordinate
end Superfusion

