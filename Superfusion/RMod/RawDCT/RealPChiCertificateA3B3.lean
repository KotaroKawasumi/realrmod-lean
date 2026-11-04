import Superfusion.RMod.RawDCT.RealPChiCertificateA3B3C0
import Superfusion.RMod.RawDCT.RealPChiCertificateA3B3C1
import Superfusion.RMod.RawDCT.RealPChiCertificateA3B3C2
import Superfusion.RMod.RawDCT.RealPChiCertificateA3B3C3
import Superfusion.RMod.RawDCT.RealPChiCertificateA3B3C4
import Superfusion.RMod.RawDCT.RealPChiCertificateA3B3C5
import Superfusion.RMod.RawDCT.RealPChiCertificateA3B3C6
import Superfusion.RMod.RawDCT.RealPChiCertificateA3B3C7

/-!
# Exact real pentagon certificate aggregate: first labels (3,3)

This file performs no fourfold calculation. It selects one of the eight
`(3,3,c)` byte leaves and dispatches to its kernel-checked law.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT
namespace RealPChiCertificate

/-- Computable target-coordinate data following labels (3,3). -/
def targetIndexA3B3 (c d : ZMod 8) : ℕ :=
  selectLabel c
    (packedByteAt targetBytesA3B3C0 d.val)
    (packedByteAt targetBytesA3B3C1 d.val)
    (packedByteAt targetBytesA3B3C2 d.val)
    (packedByteAt targetBytesA3B3C3 d.val)
    (packedByteAt targetBytesA3B3C4 d.val)
    (packedByteAt targetBytesA3B3C5 d.val)
    (packedByteAt targetBytesA3B3C6 d.val)
    (packedByteAt targetBytesA3B3C7 d.val)

/-- All 64 entries with first labels (3,3), assembled without recomputation. -/
theorem exactA3B3 (c d : ZMod 8) :
    IsExactWitness 3 3 c d 0 (targetIndexA3B3 c d) := by
  rcases label_cases c with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · unfold targetIndexA3B3 selectLabel
    rw [if_pos rfl]
    exact exactA3B3C0 d
  · unfold targetIndexA3B3 selectLabel
    rw [if_neg (by decide), if_pos rfl]
    exact exactA3B3C1 d
  · unfold targetIndexA3B3 selectLabel
    rw [if_neg (by decide), if_neg (by decide), if_pos rfl]
    exact exactA3B3C2 d
  · unfold targetIndexA3B3 selectLabel
    rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl]
    exact exactA3B3C3 d
  · unfold targetIndexA3B3 selectLabel
    rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl]
    exact exactA3B3C4 d
  · unfold targetIndexA3B3 selectLabel
    rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl]
    exact exactA3B3C5 d
  · unfold targetIndexA3B3 selectLabel
    rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl]
    exact exactA3B3C6 d
  · unfold targetIndexA3B3 selectLabel
    rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide)]
    exact exactA3B3C7 d

end RealPChiCertificate
end Superfusion.RMod.RawDCT

