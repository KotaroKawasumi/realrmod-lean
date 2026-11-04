import Superfusion.RMod.Constructive.ConnectorTableInverseAggregate

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Superfusion
namespace RModCoordinate
namespace ConnectorTableLaws

theorem inverseCertificate_6_1_0 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 6 1 0 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 6 1 0) = true := by
  decide +kernel

theorem inverseCertificate_6_1_1 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 6 1 1 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 6 1 1) = true := by
  decide +kernel

theorem inverseCertificate_6_1_2 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 6 1 2 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 6 1 2) = true := by
  decide +kernel

theorem inverseCertificate_6_1_3 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 6 1 3 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 6 1 3) = true := by
  decide +kernel

theorem inverseCertificate_6_1_4 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 6 1 4 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 6 1 4) = true := by
  decide +kernel

theorem inverseCertificate_6_1_5 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 6 1 5 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 6 1 5) = true := by
  decide +kernel

theorem inverseCertificate_6_1_6 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 6 1 6 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 6 1 6) = true := by
  decide +kernel

theorem inverseCertificate_6_1_7 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 6 1 7 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 6 1 7) = true := by
  decide +kernel

theorem inverseCertificatesForAB_six_one :
    inverseCertificatesForAB 6 1 = true := by
  apply inverseCertificatesForAB_of_each
  intro c hc
  interval_cases c
  · exact inverseCertificate_6_1_0
  · exact inverseCertificate_6_1_1
  · exact inverseCertificate_6_1_2
  · exact inverseCertificate_6_1_3
  · exact inverseCertificate_6_1_4
  · exact inverseCertificate_6_1_5
  · exact inverseCertificate_6_1_6
  · exact inverseCertificate_6_1_7

end ConnectorTableLaws
end RModCoordinate
end Superfusion
