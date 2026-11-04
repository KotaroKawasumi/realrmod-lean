import Superfusion.RMod.RawDCT.RealPChiCertificateA2B5C0
import Superfusion.RMod.RawDCT.RealPChiCertificateA2B5C1
import Superfusion.RMod.RawDCT.RealPChiCertificateA2B5C2
import Superfusion.RMod.RawDCT.RealPChiCertificateA2B5C3
import Superfusion.RMod.RawDCT.RealPChiCertificateA2B5C4
import Superfusion.RMod.RawDCT.RealPChiCertificateA2B5C5
import Superfusion.RMod.RawDCT.RealPChiCertificateA2B5C6
import Superfusion.RMod.RawDCT.RealPChiCertificateA2B5C7

/-!
# Exact real pentagon certificate aggregate: first labels (2,5)

This file performs no fourfold calculation.  It selects one of the eight
`(2,5,c)` byte leaves and dispatches to its kernel-checked law.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT
namespace RealPChiCertificate

/-- Computable target-coordinate data following labels (2,5). -/
def targetIndexA2B5 (c d : ZMod 8) : ℕ :=
  selectLabel c
    (packedByteAt targetBytesA2B5C0 d.val)
    (packedByteAt targetBytesA2B5C1 d.val)
    (packedByteAt targetBytesA2B5C2 d.val)
    (packedByteAt targetBytesA2B5C3 d.val)
    (packedByteAt targetBytesA2B5C4 d.val)
    (packedByteAt targetBytesA2B5C5 d.val)
    (packedByteAt targetBytesA2B5C6 d.val)
    (packedByteAt targetBytesA2B5C7 d.val)

/-- All 64 entries with first labels (2,5), assembled without
recomputation. -/
theorem exactA2B5 (c d : ZMod 8) :
    IsExactWitness 2 5 c d 0 (targetIndexA2B5 c d) := by
  rcases label_cases c with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · unfold targetIndexA2B5 selectLabel
    rw [if_pos rfl]
    exact exactA2B5C0 d
  · unfold targetIndexA2B5 selectLabel
    rw [if_neg (by decide), if_pos rfl]
    exact exactA2B5C1 d
  · unfold targetIndexA2B5 selectLabel
    rw [if_neg (by decide), if_neg (by decide), if_pos rfl]
    exact exactA2B5C2 d
  · unfold targetIndexA2B5 selectLabel
    rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl]
    exact exactA2B5C3 d
  · unfold targetIndexA2B5 selectLabel
    rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl]
    exact exactA2B5C4 d
  · unfold targetIndexA2B5 selectLabel
    rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl]
    exact exactA2B5C5 d
  · unfold targetIndexA2B5 selectLabel
    rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl]
    exact exactA2B5C6 d
  · unfold targetIndexA2B5 selectLabel
    rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide)]
    exact exactA2B5C7 d

end RealPChiCertificate
end Superfusion.RMod.RawDCT
