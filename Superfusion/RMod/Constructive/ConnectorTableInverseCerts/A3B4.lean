import Superfusion.RMod.Constructive.ConnectorTableInverseAggregate

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Superfusion
namespace RModCoordinate
namespace ConnectorTableLaws

theorem inverseCertificate_3_4_0 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 3 4 0 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 3 4 0) = true := by
  decide +kernel

theorem inverseCertificate_3_4_1 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 3 4 1 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 3 4 1) = true := by
  decide +kernel

theorem inverseCertificate_3_4_2 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 3 4 2 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 3 4 2) = true := by
  decide +kernel

theorem inverseCertificate_3_4_3 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 3 4 3 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 3 4 3) = true := by
  decide +kernel

theorem inverseCertificate_3_4_4 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 3 4 4 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 3 4 4) = true := by
  decide +kernel

theorem inverseCertificate_3_4_5 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 3 4 5 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 3 4 5) = true := by
  decide +kernel

theorem inverseCertificate_3_4_6 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 3 4 6 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 3 4 6) = true := by
  decide +kernel

theorem inverseCertificate_3_4_7 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 3 4 7 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 3 4 7) = true := by
  decide +kernel

theorem inverseCertificatesForAB_three_four :
    inverseCertificatesForAB 3 4 = true := by
  apply inverseCertificatesForAB_of_each
  intro c hc
  interval_cases c
  · exact inverseCertificate_3_4_0
  · exact inverseCertificate_3_4_1
  · exact inverseCertificate_3_4_2
  · exact inverseCertificate_3_4_3
  · exact inverseCertificate_3_4_4
  · exact inverseCertificate_3_4_5
  · exact inverseCertificate_3_4_6
  · exact inverseCertificate_3_4_7

end ConnectorTableLaws
end RModCoordinate
end Superfusion
