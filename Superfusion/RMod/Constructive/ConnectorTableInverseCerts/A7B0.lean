import Superfusion.RMod.Constructive.ConnectorTableInverseAggregate

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Superfusion
namespace RModCoordinate
namespace ConnectorTableLaws

theorem inverseCertificate_7_0_0 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 7 0 0 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 7 0 0) = true := by
  decide +kernel

theorem inverseCertificate_7_0_1 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 7 0 1 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 7 0 1) = true := by
  decide +kernel

theorem inverseCertificate_7_0_2 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 7 0 2 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 7 0 2) = true := by
  decide +kernel

theorem inverseCertificate_7_0_3 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 7 0 3 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 7 0 3) = true := by
  decide +kernel

theorem inverseCertificate_7_0_4 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 7 0 4 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 7 0 4) = true := by
  decide +kernel

theorem inverseCertificate_7_0_5 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 7 0 5 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 7 0 5) = true := by
  decide +kernel

theorem inverseCertificate_7_0_6 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 7 0 6 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 7 0 6) = true := by
  decide +kernel

theorem inverseCertificate_7_0_7 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 7 0 7 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 7 0 7) = true := by
  decide +kernel

theorem inverseCertificatesForAB_seven_zero :
    inverseCertificatesForAB 7 0 = true := by
  apply inverseCertificatesForAB_of_each
  intro c hc
  interval_cases c
  · exact inverseCertificate_7_0_0
  · exact inverseCertificate_7_0_1
  · exact inverseCertificate_7_0_2
  · exact inverseCertificate_7_0_3
  · exact inverseCertificate_7_0_4
  · exact inverseCertificate_7_0_5
  · exact inverseCertificate_7_0_6
  · exact inverseCertificate_7_0_7

end ConnectorTableLaws
end RModCoordinate
end Superfusion
