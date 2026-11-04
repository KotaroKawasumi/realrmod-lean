import Superfusion.RMod.RawDCT.RealPChiCertificateA6B0
import Superfusion.RMod.RawDCT.RealPChiCertificateA6B1
import Superfusion.RMod.RawDCT.RealPChiCertificateA6B2
import Superfusion.RMod.RawDCT.RealPChiCertificateA6B3
import Superfusion.RMod.RawDCT.RealPChiCertificateA6B4
import Superfusion.RMod.RawDCT.RealPChiCertificateA6B5
import Superfusion.RMod.RawDCT.RealPChiCertificateA6B6
import Superfusion.RMod.RawDCT.RealPChiCertificateA6B7

/-!
# Exact real pentagon certificate: first label 6

This aggregate contains no coefficient calculation.  It combines the eight
`(6,b)` target-data leaves and dispatches to their kernel-checked
64-point laws.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT
namespace RealPChiCertificate

/-- Computable target-coordinate data for all triples following label 6. -/
def targetIndexA6 (b c d : ZMod 8) : ℕ :=
  selectLabel b
    (packedByteAt targetBytesA6B0 (pairLeafIndex c d))
    (packedByteAt targetBytesA6B1 (pairLeafIndex c d))
    (packedByteAt targetBytesA6B2 (pairLeafIndex c d))
    (packedByteAt targetBytesA6B3 (pairLeafIndex c d))
    (packedByteAt targetBytesA6B4 (pairLeafIndex c d))
    (packedByteAt targetBytesA6B5 (pairLeafIndex c d))
    (packedByteAt targetBytesA6B6 (pairLeafIndex c d))
    (packedByteAt targetBytesA6B7 (pairLeafIndex c d))

/-- All 512 entries with first label 6, assembled without recomputation. -/
theorem exactA6 (b c d : ZMod 8) :
    IsExactWitness 6 b c d 0 (targetIndexA6 b c d) := by
  unfold targetIndexA6
  exact assembleWitness 6 b c d
    (packedByteAt targetBytesA6B0 (pairLeafIndex c d))
    (packedByteAt targetBytesA6B1 (pairLeafIndex c d))
    (packedByteAt targetBytesA6B2 (pairLeafIndex c d))
    (packedByteAt targetBytesA6B3 (pairLeafIndex c d))
    (packedByteAt targetBytesA6B4 (pairLeafIndex c d))
    (packedByteAt targetBytesA6B5 (pairLeafIndex c d))
    (packedByteAt targetBytesA6B6 (pairLeafIndex c d))
    (packedByteAt targetBytesA6B7 (pairLeafIndex c d))
    (exactA6B0 c d)
    (exactA6B1 c d)
    (exactA6B2 c d)
    (exactA6B3 c d)
    (exactA6B4 c d)
    (exactA6B5 c d)
    (exactA6B6 c d)
    (exactA6B7 c d)

end RealPChiCertificate
end Superfusion.RMod.RawDCT
