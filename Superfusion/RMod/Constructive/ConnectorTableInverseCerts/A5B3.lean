import Superfusion.RMod.Constructive.ConnectorTableInverseAggregate

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Superfusion
namespace RModCoordinate
namespace ConnectorTableLaws

theorem inverseCertificate_5_3_0 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 5 3 0 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 5 3 0) = true := by
  decide +kernel

theorem inverseCertificate_5_3_1 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 5 3 1 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 5 3 1) = true := by
  decide +kernel

theorem inverseCertificate_5_3_2 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 5 3 2 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 5 3 2) = true := by
  decide +kernel

theorem inverseCertificate_5_3_3 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 5 3 3 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 5 3 3) = true := by
  decide +kernel

theorem inverseCertificate_5_3_4 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 5 3 4 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 5 3 4) = true := by
  decide +kernel

theorem inverseCertificate_5_3_5 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 5 3 5 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 5 3 5) = true := by
  decide +kernel

theorem inverseCertificate_5_3_6 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 5 3 6 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 5 3 6) = true := by
  decide +kernel

theorem inverseCertificate_5_3_7 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 5 3 7 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 5 3 7) = true := by
  decide +kernel

theorem inverseCertificatesForAB_five_three :
    inverseCertificatesForAB 5 3 = true := by
  apply inverseCertificatesForAB_of_each
  intro c hc
  interval_cases c
  · exact inverseCertificate_5_3_0
  · exact inverseCertificate_5_3_1
  · exact inverseCertificate_5_3_2
  · exact inverseCertificate_5_3_3
  · exact inverseCertificate_5_3_4
  · exact inverseCertificate_5_3_5
  · exact inverseCertificate_5_3_6
  · exact inverseCertificate_5_3_7

end ConnectorTableLaws
end RModCoordinate
end Superfusion
