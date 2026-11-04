import Superfusion.RMod.Constructive.ConnectorTableInverseCertificate

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Superfusion
namespace RModCoordinate
namespace ConnectorTableLaws

theorem inverseCertificatesForAB_zero_zero :
    inverseCertificatesForAB 0 0 = true := by
  decide +kernel

theorem inverseCertificatesForAB_zero_one :
    inverseCertificatesForAB 0 1 = true := by
  decide +kernel

theorem inverseCertificatesForAB_zero_two :
    inverseCertificatesForAB 0 2 = true := by
  decide +kernel

theorem inverseCertificatesForAB_zero_three :
    inverseCertificatesForAB 0 3 = true := by
  decide +kernel

theorem inverseCertificatesForAB_zero_four :
    inverseCertificatesForAB 0 4 = true := by
  decide +kernel

theorem inverseCertificatesForAB_zero_five :
    inverseCertificatesForAB 0 5 = true := by
  decide +kernel

theorem inverseCertificatesForAB_zero_six :
    inverseCertificatesForAB 0 6 = true := by
  decide +kernel

theorem inverseCertificatesForAB_zero_seven :
    inverseCertificatesForAB 0 7 = true := by
  decide +kernel

end ConnectorTableLaws
end RModCoordinate
end Superfusion

