import Superfusion.RMod.RawDCT.RealPChiCertificateA7B0
import Superfusion.RMod.RawDCT.RealPChiCertificateA7B1
import Superfusion.RMod.RawDCT.RealPChiCertificateA7B2
import Superfusion.RMod.RawDCT.RealPChiCertificateA7B3
import Superfusion.RMod.RawDCT.RealPChiCertificateA7B4
import Superfusion.RMod.RawDCT.RealPChiCertificateA7B5
import Superfusion.RMod.RawDCT.RealPChiCertificateA7B6
import Superfusion.RMod.RawDCT.RealPChiCertificateA7B7

/-!
# Exact real pentagon certificate: first label 7

This aggregate contains no coefficient calculation.  It combines the eight
`(7,b)` target-data leaves and dispatches to their kernel-checked
64-point laws.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT
namespace RealPChiCertificate

/-- Computable target-coordinate data for all triples following label 7. -/
def targetIndexA7 (b c d : ZMod 8) : ℕ :=
  selectLabel b
    (packedByteAt targetBytesA7B0 (pairLeafIndex c d))
    (packedByteAt targetBytesA7B1 (pairLeafIndex c d))
    (packedByteAt targetBytesA7B2 (pairLeafIndex c d))
    (packedByteAt targetBytesA7B3 (pairLeafIndex c d))
    (packedByteAt targetBytesA7B4 (pairLeafIndex c d))
    (packedByteAt targetBytesA7B5 (pairLeafIndex c d))
    (packedByteAt targetBytesA7B6 (pairLeafIndex c d))
    (packedByteAt targetBytesA7B7 (pairLeafIndex c d))

/-- All 512 entries with first label 7, assembled without recomputation. -/
theorem exactA7 (b c d : ZMod 8) :
    IsExactWitness 7 b c d 0 (targetIndexA7 b c d) := by
  unfold targetIndexA7
  exact assembleWitness 7 b c d
    (packedByteAt targetBytesA7B0 (pairLeafIndex c d))
    (packedByteAt targetBytesA7B1 (pairLeafIndex c d))
    (packedByteAt targetBytesA7B2 (pairLeafIndex c d))
    (packedByteAt targetBytesA7B3 (pairLeafIndex c d))
    (packedByteAt targetBytesA7B4 (pairLeafIndex c d))
    (packedByteAt targetBytesA7B5 (pairLeafIndex c d))
    (packedByteAt targetBytesA7B6 (pairLeafIndex c d))
    (packedByteAt targetBytesA7B7 (pairLeafIndex c d))
    (exactA7B0 c d)
    (exactA7B1 c d)
    (exactA7B2 c d)
    (exactA7B3 c d)
    (exactA7B4 c d)
    (exactA7B5 c d)
    (exactA7B6 c d)
    (exactA7B7 c d)

end RealPChiCertificate
end Superfusion.RMod.RawDCT
