import Superfusion.RMod.Constructive.ConnectorTableInverseCertificate
import Superfusion.RMod.Constructive.ConnectorTableInverseAggregate
import Superfusion.RMod.Constructive.ConnectorTableInverseCerts.A3B3C0
import Superfusion.RMod.Constructive.ConnectorTableInverseCerts.A3B3C1
import Superfusion.RMod.Constructive.ConnectorTableInverseCerts.A3B3C2
import Superfusion.RMod.Constructive.ConnectorTableInverseCerts.A3B3C3
import Superfusion.RMod.Constructive.ConnectorTableInverseCerts.A3B3C4
import Superfusion.RMod.Constructive.ConnectorTableInverseCerts.A3B3C5
import Superfusion.RMod.Constructive.ConnectorTableInverseCerts.A3B3C6
import Superfusion.RMod.Constructive.ConnectorTableInverseCerts.A3B3C7

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Superfusion
namespace RModCoordinate
namespace ConnectorTableLaws

theorem inverseCertificatesForAB_three_three :
    inverseCertificatesForAB 3 3 = true := by
  apply inverseCertificatesForAB_of_each
  intro c hc
  interval_cases c
  · exact inverseCertificate_3_3_0
  · exact inverseCertificate_3_3_1
  · exact inverseCertificate_3_3_2
  · exact inverseCertificate_3_3_3
  · exact inverseCertificate_3_3_4
  · exact inverseCertificate_3_3_5
  · exact inverseCertificate_3_3_6
  · exact inverseCertificate_3_3_7

end ConnectorTableLaws
end RModCoordinate
end Superfusion
