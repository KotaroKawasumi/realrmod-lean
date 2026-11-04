import Superfusion.RMod.RawDCT.RealPChiCertificateA4B0
import Superfusion.RMod.RawDCT.RealPChiCertificateA4B1
import Superfusion.RMod.RawDCT.RealPChiCertificateA4B2
import Superfusion.RMod.RawDCT.RealPChiCertificateA4B3
import Superfusion.RMod.RawDCT.RealPChiCertificateA4B4
import Superfusion.RMod.RawDCT.RealPChiCertificateA4B5
import Superfusion.RMod.RawDCT.RealPChiCertificateA4B6
import Superfusion.RMod.RawDCT.RealPChiCertificateA4B7

/-!
# Exact real pentagon certificate: first label 4

This aggregate contains no coefficient calculation.  It combines the eight
`(4,b)` target-data leaves and dispatches to their kernel-checked
64-point laws.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT
namespace RealPChiCertificate

/-- Computable target-coordinate data for all triples following label 4. -/
def targetIndexA4 (b c d : ZMod 8) : ℕ :=
  selectLabel b
    (packedByteAt targetBytesA4B0 (pairLeafIndex c d))
    (packedByteAt targetBytesA4B1 (pairLeafIndex c d))
    (packedByteAt targetBytesA4B2 (pairLeafIndex c d))
    (packedByteAt targetBytesA4B3 (pairLeafIndex c d))
    (packedByteAt targetBytesA4B4 (pairLeafIndex c d))
    (packedByteAt targetBytesA4B5 (pairLeafIndex c d))
    (packedByteAt targetBytesA4B6 (pairLeafIndex c d))
    (packedByteAt targetBytesA4B7 (pairLeafIndex c d))

/-- All 512 entries with first label 4, assembled without recomputation. -/
theorem exactA4 (b c d : ZMod 8) :
    IsExactWitness 4 b c d 0 (targetIndexA4 b c d) := by
  unfold targetIndexA4
  exact assembleWitness 4 b c d
    (packedByteAt targetBytesA4B0 (pairLeafIndex c d))
    (packedByteAt targetBytesA4B1 (pairLeafIndex c d))
    (packedByteAt targetBytesA4B2 (pairLeafIndex c d))
    (packedByteAt targetBytesA4B3 (pairLeafIndex c d))
    (packedByteAt targetBytesA4B4 (pairLeafIndex c d))
    (packedByteAt targetBytesA4B5 (pairLeafIndex c d))
    (packedByteAt targetBytesA4B6 (pairLeafIndex c d))
    (packedByteAt targetBytesA4B7 (pairLeafIndex c d))
    (exactA4B0 c d)
    (exactA4B1 c d)
    (exactA4B2 c d)
    (exactA4B3 c d)
    (exactA4B4 c d)
    (exactA4B5 c d)
    (exactA4B6 c d)
    (exactA4B7 c d)

end RealPChiCertificate
end Superfusion.RMod.RawDCT
