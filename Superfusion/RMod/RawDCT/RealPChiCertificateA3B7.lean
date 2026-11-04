import Superfusion.RMod.RawDCT.RealPChiCertificateA3B7C0
import Superfusion.RMod.RawDCT.RealPChiCertificateA3B7C1
import Superfusion.RMod.RawDCT.RealPChiCertificateA3B7C2
import Superfusion.RMod.RawDCT.RealPChiCertificateA3B7C3
import Superfusion.RMod.RawDCT.RealPChiCertificateA3B7C4
import Superfusion.RMod.RawDCT.RealPChiCertificateA3B7C5
import Superfusion.RMod.RawDCT.RealPChiCertificateA3B7C6
import Superfusion.RMod.RawDCT.RealPChiCertificateA3B7C7

/-!
# Exact real pentagon certificate aggregate: first labels (3,7)

This file performs no fourfold calculation. It selects one of the eight
`(3,7,c)` byte leaves and dispatches to its kernel-checked law.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT
namespace RealPChiCertificate

/-- Computable target-coordinate data following labels (3,7). -/
def targetIndexA3B7 (c d : ZMod 8) : ℕ :=
  selectLabel c
    (packedByteAt targetBytesA3B7C0 d.val)
    (packedByteAt targetBytesA3B7C1 d.val)
    (packedByteAt targetBytesA3B7C2 d.val)
    (packedByteAt targetBytesA3B7C3 d.val)
    (packedByteAt targetBytesA3B7C4 d.val)
    (packedByteAt targetBytesA3B7C5 d.val)
    (packedByteAt targetBytesA3B7C6 d.val)
    (packedByteAt targetBytesA3B7C7 d.val)

/-- All 64 entries with first labels (3,7), assembled without recomputation. -/
theorem exactA3B7 (c d : ZMod 8) :
    IsExactWitness 3 7 c d 0 (targetIndexA3B7 c d) := by
  rcases label_cases c with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · unfold targetIndexA3B7 selectLabel
    rw [if_pos rfl]
    exact exactA3B7C0 d
  · unfold targetIndexA3B7 selectLabel
    rw [if_neg (by decide), if_pos rfl]
    exact exactA3B7C1 d
  · unfold targetIndexA3B7 selectLabel
    rw [if_neg (by decide), if_neg (by decide), if_pos rfl]
    exact exactA3B7C2 d
  · unfold targetIndexA3B7 selectLabel
    rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl]
    exact exactA3B7C3 d
  · unfold targetIndexA3B7 selectLabel
    rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl]
    exact exactA3B7C4 d
  · unfold targetIndexA3B7 selectLabel
    rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl]
    exact exactA3B7C5 d
  · unfold targetIndexA3B7 selectLabel
    rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl]
    exact exactA3B7C6 d
  · unfold targetIndexA3B7 selectLabel
    rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide)]
    exact exactA3B7C7 d

end RealPChiCertificate
end Superfusion.RMod.RawDCT

