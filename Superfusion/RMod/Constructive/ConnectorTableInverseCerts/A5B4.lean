import Superfusion.RMod.Constructive.ConnectorTableInverseAggregate

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Superfusion
namespace RModCoordinate
namespace ConnectorTableLaws

theorem inverseCertificate_5_4_0 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 5 4 0 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 5 4 0) = true := by
  decide +kernel

theorem inverseCertificate_5_4_1 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 5 4 1 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 5 4 1) = true := by
  decide +kernel

theorem inverseCertificate_5_4_2 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 5 4 2 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 5 4 2) = true := by
  decide +kernel

theorem inverseCertificate_5_4_3 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 5 4 3 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 5 4 3) = true := by
  decide +kernel

theorem inverseCertificate_5_4_4 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 5 4 4 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 5 4 4) = true := by
  decide +kernel

theorem inverseCertificate_5_4_5 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 5 4 5 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 5 4 5) = true := by
  decide +kernel

theorem inverseCertificate_5_4_6 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 5 4 6 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 5 4 6) = true := by
  decide +kernel

theorem inverseCertificate_5_4_7 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 5 4 7 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 5 4 7) = true := by
  decide +kernel

theorem inverseCertificatesForAB_five_four :
    inverseCertificatesForAB 5 4 = true := by
  apply inverseCertificatesForAB_of_each
  intro c hc
  interval_cases c
  · exact inverseCertificate_5_4_0
  · exact inverseCertificate_5_4_1
  · exact inverseCertificate_5_4_2
  · exact inverseCertificate_5_4_3
  · exact inverseCertificate_5_4_4
  · exact inverseCertificate_5_4_5
  · exact inverseCertificate_5_4_6
  · exact inverseCertificate_5_4_7

end ConnectorTableLaws
end RModCoordinate
end Superfusion
