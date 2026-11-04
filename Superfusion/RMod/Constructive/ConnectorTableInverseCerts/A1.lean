import Superfusion.RMod.Constructive.ConnectorTableInverseCertificate

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Superfusion
namespace RModCoordinate
namespace ConnectorTableLaws

theorem inverseCertificatesForAB_one_zero :
    inverseCertificatesForAB 1 0 = true := by
  decide +kernel

theorem inverseCertificatesForAB_one_one :
    inverseCertificatesForAB 1 1 = true := by
  decide +kernel

theorem inverseCertificatesForAB_one_two :
    inverseCertificatesForAB 1 2 = true := by
  decide +kernel

theorem inverseCertificatesForAB_one_three :
    inverseCertificatesForAB 1 3 = true := by
  decide +kernel

theorem inverseCertificatesForAB_one_four :
    inverseCertificatesForAB 1 4 = true := by
  decide +kernel

theorem inverseCertificatesForAB_one_five :
    inverseCertificatesForAB 1 5 = true := by
  decide +kernel

theorem inverseCertificatesForAB_one_six :
    inverseCertificatesForAB 1 6 = true := by
  decide +kernel

theorem inverseCertificatesForAB_one_seven :
    inverseCertificatesForAB 1 7 = true := by
  decide +kernel

end ConnectorTableLaws
end RModCoordinate
end Superfusion

