import Superfusion.RMod.Constructive.ConnectorTableInverseCerts.A0
import Superfusion.RMod.Constructive.ConnectorTableInverseCerts.A1
import Superfusion.RMod.Constructive.ConnectorTableInverseCerts.A2
import Superfusion.RMod.Constructive.ConnectorTableInverseCerts.A3
import Superfusion.RMod.Constructive.ConnectorTableInverseCerts.A4
import Superfusion.RMod.Constructive.ConnectorTableInverseCerts.A5
import Superfusion.RMod.Constructive.ConnectorTableInverseCerts.A6
import Superfusion.RMod.Constructive.ConnectorTableInverseCerts.A7

/-!
# Exhaustive inverse laws for the constructive connector table

This is a thin proof-only endpoint.  It combines the saved fixed-`(a,b)`
kernel certificates and exposes only the two pointwise inverse checks needed
by the raw connector construction.
-/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Superfusion
namespace RModCoordinate
namespace ConnectorTableLaws

open RMod.ConstructiveConnectorTable

/-! ## Inverse certificates, split into small fixed-`(a,b)` batches -/

private theorem inverseCertificateNat_of_batch {a b c : ℕ}
    (hbatch : inverseCertificatesForAB a b = true) (hc : c < 8) :
    checkForwardInverseNat a b c = true ∧
      checkInverseForwardNat a b c = true := by
  rw [inverseCertificatesForAB, List.all_eq_true] at hbatch
  have hand := hbatch c (List.mem_range.mpr hc)
  generalize hf : checkForwardInverseNat a b c = x at hand ⊢
  generalize hi : checkInverseForwardNat a b c = y at hand ⊢
  cases x <;> cases y <;> simp_all

private theorem inverseCertificatesForAB_true (a b : ZMod 8) :
    inverseCertificatesForAB a.val b.val = true := by
  fin_cases a <;> fin_cases b
  · exact inverseCertificatesForAB_zero_zero
  · exact inverseCertificatesForAB_zero_one
  · exact inverseCertificatesForAB_zero_two
  · exact inverseCertificatesForAB_zero_three
  · exact inverseCertificatesForAB_zero_four
  · exact inverseCertificatesForAB_zero_five
  · exact inverseCertificatesForAB_zero_six
  · exact inverseCertificatesForAB_zero_seven
  · exact inverseCertificatesForAB_one_zero
  · exact inverseCertificatesForAB_one_one
  · exact inverseCertificatesForAB_one_two
  · exact inverseCertificatesForAB_one_three
  · exact inverseCertificatesForAB_one_four
  · exact inverseCertificatesForAB_one_five
  · exact inverseCertificatesForAB_one_six
  · exact inverseCertificatesForAB_one_seven
  · exact inverseCertificatesForAB_two_zero
  · exact inverseCertificatesForAB_two_one
  · exact inverseCertificatesForAB_two_two
  · exact inverseCertificatesForAB_two_three
  · exact inverseCertificatesForAB_two_four
  · exact inverseCertificatesForAB_two_five
  · exact inverseCertificatesForAB_two_six
  · exact inverseCertificatesForAB_two_seven
  · exact inverseCertificatesForAB_three_zero
  · exact inverseCertificatesForAB_three_one
  · exact inverseCertificatesForAB_three_two
  · exact inverseCertificatesForAB_three_three
  · exact inverseCertificatesForAB_three_four
  · exact inverseCertificatesForAB_three_five
  · exact inverseCertificatesForAB_three_six
  · exact inverseCertificatesForAB_three_seven
  · exact inverseCertificatesForAB_four_zero
  · exact inverseCertificatesForAB_four_one
  · exact inverseCertificatesForAB_four_two
  · exact inverseCertificatesForAB_four_three
  · exact inverseCertificatesForAB_four_four
  · exact inverseCertificatesForAB_four_five
  · exact inverseCertificatesForAB_four_six
  · exact inverseCertificatesForAB_four_seven
  · exact inverseCertificatesForAB_five_zero
  · exact inverseCertificatesForAB_five_one
  · exact inverseCertificatesForAB_five_two
  · exact inverseCertificatesForAB_five_three
  · exact inverseCertificatesForAB_five_four
  · exact inverseCertificatesForAB_five_five
  · exact inverseCertificatesForAB_five_six
  · exact inverseCertificatesForAB_five_seven
  · exact inverseCertificatesForAB_six_zero
  · exact inverseCertificatesForAB_six_one
  · exact inverseCertificatesForAB_six_two
  · exact inverseCertificatesForAB_six_three
  · exact inverseCertificatesForAB_six_four
  · exact inverseCertificatesForAB_six_five
  · exact inverseCertificatesForAB_six_six
  · exact inverseCertificatesForAB_six_seven
  · exact inverseCertificatesForAB_seven_zero
  · exact inverseCertificatesForAB_seven_one
  · exact inverseCertificatesForAB_seven_two
  · exact inverseCertificatesForAB_seven_three
  · exact inverseCertificatesForAB_seven_four
  · exact inverseCertificatesForAB_seven_five
  · exact inverseCertificatesForAB_seven_six
  · exact inverseCertificatesForAB_seven_seven

/-- The checked raw connector matrix times its explicit conjugate-transpose
numerator is `lambda I`, at every one of the 512 label triples. -/
theorem checkForwardInverse_true (a b c : ZMod 8) :
    checkForwardInverseNat a.val b.val c.val = true := by
  exact (inverseCertificateNat_of_batch
    (inverseCertificatesForAB_true a b) (ZMod.val_lt c)).1

/-- The explicit conjugate-transpose numerator times the checked raw
connector matrix is `lambda I`, at every label triple. -/
theorem checkInverseForward_true (a b c : ZMod 8) :
    checkInverseForwardNat a.val b.val c.val = true := by
  exact (inverseCertificateNat_of_batch
    (inverseCertificatesForAB_true a b) (ZMod.val_lt c)).2

end ConnectorTableLaws
end RModCoordinate
end Superfusion
