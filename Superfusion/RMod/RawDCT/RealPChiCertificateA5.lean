import Superfusion.RMod.RawDCT.RealPChiCertificateA5B0
import Superfusion.RMod.RawDCT.RealPChiCertificateA5B1
import Superfusion.RMod.RawDCT.RealPChiCertificateA5B2
import Superfusion.RMod.RawDCT.RealPChiCertificateA5B3
import Superfusion.RMod.RawDCT.RealPChiCertificateA5B4
import Superfusion.RMod.RawDCT.RealPChiCertificateA5B5
import Superfusion.RMod.RawDCT.RealPChiCertificateA5B6
import Superfusion.RMod.RawDCT.RealPChiCertificateA5B7

/-!
# Exact real pentagon certificate: first label 5

This aggregate contains no coefficient calculation.  It combines the eight
`(5,b)` target-data leaves and dispatches to their kernel-checked
64-point laws.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT
namespace RealPChiCertificate

/-- Computable target-coordinate data for all triples following label 5. -/
def targetIndexA5 (b c d : ZMod 8) : ℕ :=
  selectLabel b
    (packedByteAt targetBytesA5B0 (pairLeafIndex c d))
    (packedByteAt targetBytesA5B1 (pairLeafIndex c d))
    (targetIndexA5B2 c d)
    (targetIndexA5B3 c d)
    (targetIndexA5B4 c d)
    (targetIndexA5B5 c d)
    (packedByteAt targetBytesA5B6 (pairLeafIndex c d))
    (packedByteAt targetBytesA5B7 (pairLeafIndex c d))

/-- All 512 entries with first label 5, assembled without recomputation. -/
theorem exactA5 (b c d : ZMod 8) :
    IsExactWitness 5 b c d 0 (targetIndexA5 b c d) := by
  unfold targetIndexA5
  exact assembleWitness 5 b c d
    (packedByteAt targetBytesA5B0 (pairLeafIndex c d))
    (packedByteAt targetBytesA5B1 (pairLeafIndex c d))
    (targetIndexA5B2 c d)
    (targetIndexA5B3 c d)
    (targetIndexA5B4 c d)
    (targetIndexA5B5 c d)
    (packedByteAt targetBytesA5B6 (pairLeafIndex c d))
    (packedByteAt targetBytesA5B7 (pairLeafIndex c d))
    (exactA5B0 c d)
    (exactA5B1 c d)
    (exactA5B2 c d)
    (exactA5B3 c d)
    (exactA5B4 c d)
    (exactA5B5 c d)
    (exactA5B6 c d)
    (exactA5B7 c d)

end RealPChiCertificate
end Superfusion.RMod.RawDCT
