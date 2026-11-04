import Superfusion.RMod.RawDCT.RealPChiCertificateA0B0
import Superfusion.RMod.RawDCT.RealPChiCertificateA0B1
import Superfusion.RMod.RawDCT.RealPChiCertificateA0B2
import Superfusion.RMod.RawDCT.RealPChiCertificateA0B3
import Superfusion.RMod.RawDCT.RealPChiCertificateA0B4
import Superfusion.RMod.RawDCT.RealPChiCertificateA0B5
import Superfusion.RMod.RawDCT.RealPChiCertificateA0B6
import Superfusion.RMod.RawDCT.RealPChiCertificateA0B7

/-!
# Exact real pentagon certificate: first label 0

This aggregate contains no coefficient calculation.  It combines the eight
`(0,b)` target-data leaves and dispatches to their kernel-checked
64-point laws.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT
namespace RealPChiCertificate

/-- Computable target-coordinate data for all triples following label 0. -/
def targetIndexA0 (b c d : ZMod 8) : ℕ :=
  selectLabel b
    (packedByteAt targetBytesA0B0 (pairLeafIndex c d))
    (packedByteAt targetBytesA0B1 (pairLeafIndex c d))
    (packedByteAt targetBytesA0B2 (pairLeafIndex c d))
    (packedByteAt targetBytesA0B3 (pairLeafIndex c d))
    (packedByteAt targetBytesA0B4 (pairLeafIndex c d))
    (packedByteAt targetBytesA0B5 (pairLeafIndex c d))
    (packedByteAt targetBytesA0B6 (pairLeafIndex c d))
    (packedByteAt targetBytesA0B7 (pairLeafIndex c d))

/-- All 512 entries with first label 0, assembled without recomputation. -/
theorem exactA0 (b c d : ZMod 8) :
    IsExactWitness 0 b c d 0 (targetIndexA0 b c d) := by
  unfold targetIndexA0
  exact assembleWitness 0 b c d
    (packedByteAt targetBytesA0B0 (pairLeafIndex c d))
    (packedByteAt targetBytesA0B1 (pairLeafIndex c d))
    (packedByteAt targetBytesA0B2 (pairLeafIndex c d))
    (packedByteAt targetBytesA0B3 (pairLeafIndex c d))
    (packedByteAt targetBytesA0B4 (pairLeafIndex c d))
    (packedByteAt targetBytesA0B5 (pairLeafIndex c d))
    (packedByteAt targetBytesA0B6 (pairLeafIndex c d))
    (packedByteAt targetBytesA0B7 (pairLeafIndex c d))
    (exactA0B0 c d)
    (exactA0B1 c d)
    (exactA0B2 c d)
    (exactA0B3 c d)
    (exactA0B4 c d)
    (exactA0B5 c d)
    (exactA0B6 c d)
    (exactA0B7 c d)

end RealPChiCertificate
end Superfusion.RMod.RawDCT
