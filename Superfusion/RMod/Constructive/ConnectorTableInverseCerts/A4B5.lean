import Superfusion.RMod.Constructive.ConnectorTableInverseAggregate

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Superfusion
namespace RModCoordinate
namespace ConnectorTableLaws

theorem inverseCertificate_4_5_0 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 4 5 0 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 4 5 0) = true := by
  decide +kernel

theorem inverseCertificate_4_5_1 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 4 5 1 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 4 5 1) = true := by
  decide +kernel

theorem inverseCertificate_4_5_2 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 4 5 2 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 4 5 2) = true := by
  decide +kernel

theorem inverseCertificate_4_5_3 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 4 5 3 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 4 5 3) = true := by
  decide +kernel

theorem inverseCertificate_4_5_4 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 4 5 4 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 4 5 4) = true := by
  decide +kernel

theorem inverseCertificate_4_5_5 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 4 5 5 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 4 5 5) = true := by
  decide +kernel

theorem inverseCertificate_4_5_6 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 4 5 6 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 4 5 6) = true := by
  decide +kernel

theorem inverseCertificate_4_5_7 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 4 5 7 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 4 5 7) = true := by
  decide +kernel

theorem inverseCertificatesForAB_four_five :
    inverseCertificatesForAB 4 5 = true := by
  apply inverseCertificatesForAB_of_each
  intro c hc
  interval_cases c
  · exact inverseCertificate_4_5_0
  · exact inverseCertificate_4_5_1
  · exact inverseCertificate_4_5_2
  · exact inverseCertificate_4_5_3
  · exact inverseCertificate_4_5_4
  · exact inverseCertificate_4_5_5
  · exact inverseCertificate_4_5_6
  · exact inverseCertificate_4_5_7

end ConnectorTableLaws
end RModCoordinate
end Superfusion
