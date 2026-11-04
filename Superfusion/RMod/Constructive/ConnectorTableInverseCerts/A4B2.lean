import Superfusion.RMod.Constructive.ConnectorTableInverseAggregate

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Superfusion
namespace RModCoordinate
namespace ConnectorTableLaws

theorem inverseCertificate_4_2_0 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 4 2 0 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 4 2 0) = true := by
  decide +kernel

theorem inverseCertificate_4_2_1 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 4 2 1 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 4 2 1) = true := by
  decide +kernel

theorem inverseCertificate_4_2_2 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 4 2 2 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 4 2 2) = true := by
  decide +kernel

theorem inverseCertificate_4_2_3 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 4 2 3 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 4 2 3) = true := by
  decide +kernel

theorem inverseCertificate_4_2_4 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 4 2 4 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 4 2 4) = true := by
  decide +kernel

theorem inverseCertificate_4_2_5 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 4 2 5 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 4 2 5) = true := by
  decide +kernel

theorem inverseCertificate_4_2_6 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 4 2 6 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 4 2 6) = true := by
  decide +kernel

theorem inverseCertificate_4_2_7 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 4 2 7 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 4 2 7) = true := by
  decide +kernel

theorem inverseCertificatesForAB_four_two :
    inverseCertificatesForAB 4 2 = true := by
  apply inverseCertificatesForAB_of_each
  intro c hc
  interval_cases c
  · exact inverseCertificate_4_2_0
  · exact inverseCertificate_4_2_1
  · exact inverseCertificate_4_2_2
  · exact inverseCertificate_4_2_3
  · exact inverseCertificate_4_2_4
  · exact inverseCertificate_4_2_5
  · exact inverseCertificate_4_2_6
  · exact inverseCertificate_4_2_7

end ConnectorTableLaws
end RModCoordinate
end Superfusion
