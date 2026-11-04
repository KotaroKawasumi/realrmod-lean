import Superfusion.RMod.RawDCT.RealPChiCertificateA3B0
import Superfusion.RMod.RawDCT.RealPChiCertificateA3B1
import Superfusion.RMod.RawDCT.RealPChiCertificateA3B2
import Superfusion.RMod.RawDCT.RealPChiCertificateA3B3
import Superfusion.RMod.RawDCT.RealPChiCertificateA3B4
import Superfusion.RMod.RawDCT.RealPChiCertificateA3B5
import Superfusion.RMod.RawDCT.RealPChiCertificateA3B6
import Superfusion.RMod.RawDCT.RealPChiCertificateA3B7

/-!
# Exact real pentagon certificate: first label 3

This aggregate contains no coefficient calculation.  It combines the eight
`(3,b)` target-data leaves and dispatches to their kernel-checked
64-point laws.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT
namespace RealPChiCertificate

/-- Computable target-coordinate data for all triples following label 3. -/
def targetIndexA3 (b c d : ZMod 8) : ℕ :=
  selectLabel b
    (packedByteAt targetBytesA3B0 (pairLeafIndex c d))
    (packedByteAt targetBytesA3B1 (pairLeafIndex c d))
    (packedByteAt targetBytesA3B2 (pairLeafIndex c d))
    (targetIndexA3B3 c d)
    (packedByteAt targetBytesA3B4 (pairLeafIndex c d))
    (targetIndexA3B5 c d)
    (targetIndexA3B6 c d)
    (targetIndexA3B7 c d)

/-- All 512 entries with first label 3, assembled without recomputation. -/
theorem exactA3 (b c d : ZMod 8) :
    IsExactWitness 3 b c d 0 (targetIndexA3 b c d) := by
  unfold targetIndexA3
  exact assembleWitness 3 b c d
    (packedByteAt targetBytesA3B0 (pairLeafIndex c d))
    (packedByteAt targetBytesA3B1 (pairLeafIndex c d))
    (packedByteAt targetBytesA3B2 (pairLeafIndex c d))
    (targetIndexA3B3 c d)
    (packedByteAt targetBytesA3B4 (pairLeafIndex c d))
    (targetIndexA3B5 c d)
    (targetIndexA3B6 c d)
    (targetIndexA3B7 c d)
    (exactA3B0 c d)
    (exactA3B1 c d)
    (exactA3B2 c d)
    (exactA3B3 c d)
    (exactA3B4 c d)
    (exactA3B5 c d)
    (exactA3B6 c d)
    (exactA3B7 c d)

end RealPChiCertificate
end Superfusion.RMod.RawDCT
