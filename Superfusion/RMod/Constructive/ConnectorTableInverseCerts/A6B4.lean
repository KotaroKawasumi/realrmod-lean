import Superfusion.RMod.Constructive.ConnectorTableInverseAggregate

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Superfusion
namespace RModCoordinate
namespace ConnectorTableLaws

theorem inverseCertificate_6_4_0 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 6 4 0 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 6 4 0) = true := by
  decide +kernel

theorem inverseCertificate_6_4_1 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 6 4 1 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 6 4 1) = true := by
  decide +kernel

theorem inverseCertificate_6_4_2 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 6 4 2 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 6 4 2) = true := by
  decide +kernel

theorem inverseCertificate_6_4_3 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 6 4 3 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 6 4 3) = true := by
  decide +kernel

theorem inverseCertificate_6_4_4 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 6 4 4 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 6 4 4) = true := by
  decide +kernel

theorem inverseCertificate_6_4_5 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 6 4 5 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 6 4 5) = true := by
  decide +kernel

theorem inverseCertificate_6_4_6 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 6 4 6 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 6 4 6) = true := by
  decide +kernel

theorem inverseCertificate_6_4_7 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 6 4 7 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 6 4 7) = true := by
  decide +kernel

theorem inverseCertificatesForAB_six_four :
    inverseCertificatesForAB 6 4 = true := by
  apply inverseCertificatesForAB_of_each
  intro c hc
  interval_cases c
  · exact inverseCertificate_6_4_0
  · exact inverseCertificate_6_4_1
  · exact inverseCertificate_6_4_2
  · exact inverseCertificate_6_4_3
  · exact inverseCertificate_6_4_4
  · exact inverseCertificate_6_4_5
  · exact inverseCertificate_6_4_6
  · exact inverseCertificate_6_4_7

end ConnectorTableLaws
end RModCoordinate
end Superfusion
