import Superfusion.RMod.RawDCT.RealPChiCertificateA2B0
import Superfusion.RMod.RawDCT.RealPChiCertificateA2B1
import Superfusion.RMod.RawDCT.RealPChiCertificateA2B2
import Superfusion.RMod.RawDCT.RealPChiCertificateA2B3
import Superfusion.RMod.RawDCT.RealPChiCertificateA2B4
import Superfusion.RMod.RawDCT.RealPChiCertificateA2B5
import Superfusion.RMod.RawDCT.RealPChiCertificateA2B6
import Superfusion.RMod.RawDCT.RealPChiCertificateA2B7

/-!
# Exact real pentagon certificate: first label 2

This aggregate contains no coefficient calculation.  It combines the eight
`(2,b)` target-data leaves and dispatches to their kernel-checked
64-point laws.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT
namespace RealPChiCertificate

/-- Computable target-coordinate data for all triples following label 2. -/
def targetIndexA2 (b c d : ZMod 8) : ℕ :=
  selectLabel b
    (packedByteAt targetBytesA2B0 (pairLeafIndex c d))
    (packedByteAt targetBytesA2B1 (pairLeafIndex c d))
    (packedByteAt targetBytesA2B2 (pairLeafIndex c d))
    (packedByteAt targetBytesA2B3 (pairLeafIndex c d))
    (packedByteAt targetBytesA2B4 (pairLeafIndex c d))
    (targetIndexA2B5 c d)
    (packedByteAt targetBytesA2B6 (pairLeafIndex c d))
    (targetIndexA2B7 c d)

/-- All 512 entries with first label 2, assembled without recomputation. -/
theorem exactA2 (b c d : ZMod 8) :
    IsExactWitness 2 b c d 0 (targetIndexA2 b c d) := by
  unfold targetIndexA2
  exact assembleWitness 2 b c d
    (packedByteAt targetBytesA2B0 (pairLeafIndex c d))
    (packedByteAt targetBytesA2B1 (pairLeafIndex c d))
    (packedByteAt targetBytesA2B2 (pairLeafIndex c d))
    (packedByteAt targetBytesA2B3 (pairLeafIndex c d))
    (packedByteAt targetBytesA2B4 (pairLeafIndex c d))
    (targetIndexA2B5 c d)
    (packedByteAt targetBytesA2B6 (pairLeafIndex c d))
    (targetIndexA2B7 c d)
    (exactA2B0 c d)
    (exactA2B1 c d)
    (exactA2B2 c d)
    (exactA2B3 c d)
    (exactA2B4 c d)
    (exactA2B5 c d)
    (exactA2B6 c d)
    (exactA2B7 c d)

end RealPChiCertificate
end Superfusion.RMod.RawDCT
