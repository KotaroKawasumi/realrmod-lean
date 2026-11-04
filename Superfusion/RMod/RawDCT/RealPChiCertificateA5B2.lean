import Superfusion.RMod.RawDCT.RealPChiCertificateA5B2C0
import Superfusion.RMod.RawDCT.RealPChiCertificateA5B2C1
import Superfusion.RMod.RawDCT.RealPChiCertificateA5B2C2
import Superfusion.RMod.RawDCT.RealPChiCertificateA5B2C3
import Superfusion.RMod.RawDCT.RealPChiCertificateA5B2C4
import Superfusion.RMod.RawDCT.RealPChiCertificateA5B2C5
import Superfusion.RMod.RawDCT.RealPChiCertificateA5B2C6
import Superfusion.RMod.RawDCT.RealPChiCertificateA5B2C7

/-!
# Exact real pentagon certificate aggregate: first labels (5,2)

This file performs no fourfold calculation. It selects one of the eight
`(5,2,c)` byte leaves and dispatches to its kernel-checked law.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT
namespace RealPChiCertificate

/-- Computable target-coordinate data following labels (5,2). -/
def targetIndexA5B2 (c d : ZMod 8) : ℕ :=
  selectLabel c
    (packedByteAt targetBytesA5B2C0 d.val)
    (packedByteAt targetBytesA5B2C1 d.val)
    (packedByteAt targetBytesA5B2C2 d.val)
    (packedByteAt targetBytesA5B2C3 d.val)
    (packedByteAt targetBytesA5B2C4 d.val)
    (packedByteAt targetBytesA5B2C5 d.val)
    (packedByteAt targetBytesA5B2C6 d.val)
    (packedByteAt targetBytesA5B2C7 d.val)

/-- All 64 entries with first labels (5,2), assembled without recomputation. -/
theorem exactA5B2 (c d : ZMod 8) :
    IsExactWitness 5 2 c d 0 (targetIndexA5B2 c d) := by
  rcases label_cases c with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · unfold targetIndexA5B2 selectLabel
    rw [if_pos rfl]
    exact exactA5B2C0 d
  · unfold targetIndexA5B2 selectLabel
    rw [if_neg (by decide), if_pos rfl]
    exact exactA5B2C1 d
  · unfold targetIndexA5B2 selectLabel
    rw [if_neg (by decide), if_neg (by decide), if_pos rfl]
    exact exactA5B2C2 d
  · unfold targetIndexA5B2 selectLabel
    rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl]
    exact exactA5B2C3 d
  · unfold targetIndexA5B2 selectLabel
    rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl]
    exact exactA5B2C4 d
  · unfold targetIndexA5B2 selectLabel
    rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl]
    exact exactA5B2C5 d
  · unfold targetIndexA5B2 selectLabel
    rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl]
    exact exactA5B2C6 d
  · unfold targetIndexA5B2 selectLabel
    rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide)]
    exact exactA5B2C7 d

end RealPChiCertificate
end Superfusion.RMod.RawDCT

