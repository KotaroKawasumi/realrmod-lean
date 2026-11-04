import Superfusion.RMod.Constructive.ConnectorTableInverseAggregate

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Superfusion
namespace RModCoordinate
namespace ConnectorTableLaws

theorem inverseCertificate_4_7_0 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 4 7 0 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 4 7 0) = true := by
  decide +kernel

theorem inverseCertificate_4_7_1 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 4 7 1 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 4 7 1) = true := by
  decide +kernel

theorem inverseCertificate_4_7_2 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 4 7 2 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 4 7 2) = true := by
  decide +kernel

theorem inverseCertificate_4_7_3 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 4 7 3 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 4 7 3) = true := by
  decide +kernel

theorem inverseCertificate_4_7_4 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 4 7 4 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 4 7 4) = true := by
  decide +kernel

theorem inverseCertificate_4_7_5 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 4 7 5 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 4 7 5) = true := by
  decide +kernel

theorem inverseCertificate_4_7_6 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 4 7 6 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 4 7 6) = true := by
  decide +kernel

theorem inverseCertificate_4_7_7 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 4 7 7 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 4 7 7) = true := by
  decide +kernel

theorem inverseCertificatesForAB_four_seven :
    inverseCertificatesForAB 4 7 = true := by
  apply inverseCertificatesForAB_of_each
  intro c hc
  interval_cases c
  · exact inverseCertificate_4_7_0
  · exact inverseCertificate_4_7_1
  · exact inverseCertificate_4_7_2
  · exact inverseCertificate_4_7_3
  · exact inverseCertificate_4_7_4
  · exact inverseCertificate_4_7_5
  · exact inverseCertificate_4_7_6
  · exact inverseCertificate_4_7_7

end ConnectorTableLaws
end RModCoordinate
end Superfusion
