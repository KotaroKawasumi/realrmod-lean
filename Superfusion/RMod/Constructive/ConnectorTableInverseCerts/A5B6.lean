import Superfusion.RMod.Constructive.ConnectorTableInverseAggregate

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Superfusion
namespace RModCoordinate
namespace ConnectorTableLaws

theorem inverseCertificate_5_6_0 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 5 6 0 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 5 6 0) = true := by
  decide +kernel

theorem inverseCertificate_5_6_1 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 5 6 1 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 5 6 1) = true := by
  decide +kernel

theorem inverseCertificate_5_6_2 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 5 6 2 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 5 6 2) = true := by
  decide +kernel

theorem inverseCertificate_5_6_3 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 5 6 3 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 5 6 3) = true := by
  decide +kernel

theorem inverseCertificate_5_6_4 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 5 6 4 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 5 6 4) = true := by
  decide +kernel

theorem inverseCertificate_5_6_5 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 5 6 5 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 5 6 5) = true := by
  decide +kernel

theorem inverseCertificate_5_6_6 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 5 6 6 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 5 6 6) = true := by
  decide +kernel

theorem inverseCertificate_5_6_7 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 5 6 7 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 5 6 7) = true := by
  decide +kernel

theorem inverseCertificatesForAB_five_six :
    inverseCertificatesForAB 5 6 = true := by
  apply inverseCertificatesForAB_of_each
  intro c hc
  interval_cases c
  · exact inverseCertificate_5_6_0
  · exact inverseCertificate_5_6_1
  · exact inverseCertificate_5_6_2
  · exact inverseCertificate_5_6_3
  · exact inverseCertificate_5_6_4
  · exact inverseCertificate_5_6_5
  · exact inverseCertificate_5_6_6
  · exact inverseCertificate_5_6_7

end ConnectorTableLaws
end RModCoordinate
end Superfusion
