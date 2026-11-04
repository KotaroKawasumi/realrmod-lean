import Superfusion.RMod.RawDCT.RealPChiCertificateA1B0
import Superfusion.RMod.RawDCT.RealPChiCertificateA1B1
import Superfusion.RMod.RawDCT.RealPChiCertificateA1B2
import Superfusion.RMod.RawDCT.RealPChiCertificateA1B3
import Superfusion.RMod.RawDCT.RealPChiCertificateA1B4
import Superfusion.RMod.RawDCT.RealPChiCertificateA1B5
import Superfusion.RMod.RawDCT.RealPChiCertificateA1B6
import Superfusion.RMod.RawDCT.RealPChiCertificateA1B7

/-!
# Exact real pentagon certificate: first label 1

This aggregate contains no coefficient calculation.  It combines the eight
`(1,b)` target-data leaves and dispatches to their kernel-checked
64-point laws.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT
namespace RealPChiCertificate

/-- Computable target-coordinate data for all triples following label 1. -/
def targetIndexA1 (b c d : ZMod 8) : ℕ :=
  selectLabel b
    (packedByteAt targetBytesA1B0 (pairLeafIndex c d))
    (packedByteAt targetBytesA1B1 (pairLeafIndex c d))
    (packedByteAt targetBytesA1B2 (pairLeafIndex c d))
    (packedByteAt targetBytesA1B3 (pairLeafIndex c d))
    (packedByteAt targetBytesA1B4 (pairLeafIndex c d))
    (packedByteAt targetBytesA1B5 (pairLeafIndex c d))
    (packedByteAt targetBytesA1B6 (pairLeafIndex c d))
    (packedByteAt targetBytesA1B7 (pairLeafIndex c d))

/-- All 512 entries with first label 1, assembled without recomputation. -/
theorem exactA1 (b c d : ZMod 8) :
    IsExactWitness 1 b c d 0 (targetIndexA1 b c d) := by
  unfold targetIndexA1
  exact assembleWitness 1 b c d
    (packedByteAt targetBytesA1B0 (pairLeafIndex c d))
    (packedByteAt targetBytesA1B1 (pairLeafIndex c d))
    (packedByteAt targetBytesA1B2 (pairLeafIndex c d))
    (packedByteAt targetBytesA1B3 (pairLeafIndex c d))
    (packedByteAt targetBytesA1B4 (pairLeafIndex c d))
    (packedByteAt targetBytesA1B5 (pairLeafIndex c d))
    (packedByteAt targetBytesA1B6 (pairLeafIndex c d))
    (packedByteAt targetBytesA1B7 (pairLeafIndex c d))
    (exactA1B0 c d)
    (exactA1B1 c d)
    (exactA1B2 c d)
    (exactA1B3 c d)
    (exactA1B4 c d)
    (exactA1B5 c d)
    (exactA1B6 c d)
    (exactA1B7 c d)

end RealPChiCertificate
end Superfusion.RMod.RawDCT
