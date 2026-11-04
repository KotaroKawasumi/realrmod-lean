import Superfusion.RMod.Constructive.ConnectorTableInverseCertificate

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Superfusion
namespace RModCoordinate
namespace ConnectorTableLaws

theorem inverseCertificatesForAB_two_zero :
    inverseCertificatesForAB 2 0 = true := by
  decide +kernel

theorem inverseCertificatesForAB_two_one :
    inverseCertificatesForAB 2 1 = true := by
  decide +kernel

theorem inverseCertificatesForAB_two_two :
    inverseCertificatesForAB 2 2 = true := by
  decide +kernel

theorem inverseCertificatesForAB_two_three :
    inverseCertificatesForAB 2 3 = true := by
  decide +kernel

theorem inverseCertificatesForAB_two_four :
    inverseCertificatesForAB 2 4 = true := by
  decide +kernel

theorem inverseCertificatesForAB_two_five :
    inverseCertificatesForAB 2 5 = true := by
  decide +kernel

theorem inverseCertificatesForAB_two_six :
    inverseCertificatesForAB 2 6 = true := by
  decide +kernel

theorem inverseCertificatesForAB_two_seven :
    inverseCertificatesForAB 2 7 = true := by
  decide +kernel

end ConnectorTableLaws
end RModCoordinate
end Superfusion

