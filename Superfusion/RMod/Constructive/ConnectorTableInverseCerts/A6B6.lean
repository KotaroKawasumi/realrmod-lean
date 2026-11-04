import Superfusion.RMod.Constructive.ConnectorTableInverseAggregate

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Superfusion
namespace RModCoordinate
namespace ConnectorTableLaws

theorem inverseCertificate_6_6_0 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 6 6 0 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 6 6 0) = true := by
  decide +kernel

theorem inverseCertificate_6_6_1 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 6 6 1 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 6 6 1) = true := by
  decide +kernel

theorem inverseCertificate_6_6_2 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 6 6 2 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 6 6 2) = true := by
  decide +kernel

theorem inverseCertificate_6_6_3 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 6 6 3 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 6 6 3) = true := by
  decide +kernel

theorem inverseCertificate_6_6_4 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 6 6 4 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 6 6 4) = true := by
  decide +kernel

theorem inverseCertificate_6_6_5 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 6 6 5 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 6 6 5) = true := by
  decide +kernel

theorem inverseCertificate_6_6_6 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 6 6 6 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 6 6 6) = true := by
  decide +kernel

theorem inverseCertificate_6_6_7 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 6 6 7 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 6 6 7) = true := by
  decide +kernel

theorem inverseCertificatesForAB_six_six :
    inverseCertificatesForAB 6 6 = true := by
  apply inverseCertificatesForAB_of_each
  intro c hc
  interval_cases c
  · exact inverseCertificate_6_6_0
  · exact inverseCertificate_6_6_1
  · exact inverseCertificate_6_6_2
  · exact inverseCertificate_6_6_3
  · exact inverseCertificate_6_6_4
  · exact inverseCertificate_6_6_5
  · exact inverseCertificate_6_6_6
  · exact inverseCertificate_6_6_7

end ConnectorTableLaws
end RModCoordinate
end Superfusion
