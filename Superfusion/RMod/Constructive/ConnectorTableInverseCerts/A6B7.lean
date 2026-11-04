import Superfusion.RMod.Constructive.ConnectorTableInverseAggregate

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Superfusion
namespace RModCoordinate
namespace ConnectorTableLaws

theorem inverseCertificate_6_7_0 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 6 7 0 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 6 7 0) = true := by
  decide +kernel

theorem inverseCertificate_6_7_1 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 6 7 1 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 6 7 1) = true := by
  decide +kernel

theorem inverseCertificate_6_7_2 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 6 7 2 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 6 7 2) = true := by
  decide +kernel

theorem inverseCertificate_6_7_3 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 6 7 3 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 6 7 3) = true := by
  decide +kernel

theorem inverseCertificate_6_7_4 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 6 7 4 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 6 7 4) = true := by
  decide +kernel

theorem inverseCertificate_6_7_5 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 6 7 5 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 6 7 5) = true := by
  decide +kernel

theorem inverseCertificate_6_7_6 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 6 7 6 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 6 7 6) = true := by
  decide +kernel

theorem inverseCertificate_6_7_7 :
    (RMod.ConstructiveConnectorTable.checkForwardInverseNat 6 7 7 &&
      RMod.ConstructiveConnectorTable.checkInverseForwardNat 6 7 7) = true := by
  decide +kernel

theorem inverseCertificatesForAB_six_seven :
    inverseCertificatesForAB 6 7 = true := by
  apply inverseCertificatesForAB_of_each
  intro c hc
  interval_cases c
  · exact inverseCertificate_6_7_0
  · exact inverseCertificate_6_7_1
  · exact inverseCertificate_6_7_2
  · exact inverseCertificate_6_7_3
  · exact inverseCertificate_6_7_4
  · exact inverseCertificate_6_7_5
  · exact inverseCertificate_6_7_6
  · exact inverseCertificate_6_7_7

end ConnectorTableLaws
end RModCoordinate
end Superfusion
