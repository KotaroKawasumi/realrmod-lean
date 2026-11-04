import Superfusion.RMod.Constructive.ConnectorTableInverseAggregate

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Superfusion
namespace RModCoordinate
namespace ConnectorTableLaws

theorem inverseCertificate_7_6_0 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 7 6 0 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 7 6 0) = true := by
  decide +kernel

theorem inverseCertificate_7_6_1 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 7 6 1 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 7 6 1) = true := by
  decide +kernel

theorem inverseCertificate_7_6_2 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 7 6 2 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 7 6 2) = true := by
  decide +kernel

theorem inverseCertificate_7_6_3 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 7 6 3 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 7 6 3) = true := by
  decide +kernel

theorem inverseCertificate_7_6_4 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 7 6 4 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 7 6 4) = true := by
  decide +kernel

theorem inverseCertificate_7_6_5 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 7 6 5 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 7 6 5) = true := by
  decide +kernel

theorem inverseCertificate_7_6_6 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 7 6 6 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 7 6 6) = true := by
  decide +kernel

theorem inverseCertificate_7_6_7 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 7 6 7 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 7 6 7) = true := by
  decide +kernel

theorem inverseCertificatesForAB_seven_six :
    inverseCertificatesForAB 7 6 = true := by
  apply inverseCertificatesForAB_of_each
  intro c hc
  interval_cases c
  · exact inverseCertificate_7_6_0
  · exact inverseCertificate_7_6_1
  · exact inverseCertificate_7_6_2
  · exact inverseCertificate_7_6_3
  · exact inverseCertificate_7_6_4
  · exact inverseCertificate_7_6_5
  · exact inverseCertificate_7_6_6
  · exact inverseCertificate_7_6_7

end ConnectorTableLaws
end RModCoordinate
end Superfusion
