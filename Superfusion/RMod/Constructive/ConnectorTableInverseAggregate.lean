import Superfusion.RMod.Constructive.ConnectorTableInverseCertificate

set_option autoImplicit false

namespace Superfusion
namespace RModCoordinate
namespace ConnectorTableLaws

open RMod.ConstructiveConnectorTable

theorem inverseCertificatesForAB_of_each {a b : ℕ}
    (h : ∀ c, c < 8 →
      (checkForwardInverseNat a b c && checkInverseForwardNat a b c) = true) :
    inverseCertificatesForAB a b = true := by
  rw [inverseCertificatesForAB, List.all_eq_true]
  intro c hc
  exact h c (List.mem_range.mp hc)

end ConnectorTableLaws
end RModCoordinate
end Superfusion
