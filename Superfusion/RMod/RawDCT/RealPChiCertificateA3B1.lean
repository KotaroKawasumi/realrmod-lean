import Superfusion.RMod.RawDCT.RealPChiCertificateCore

/-!
# Exact real pentagon certificate leaf: first labels (3,1)

The packed bytes are candidate target coordinates extracted by the existing
exact certgen BOT scan.  The theorem independently rechecks the actual
realTData.hom TOP/BOT coefficients with decide +kernel.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT
namespace RealPChiCertificate

/-! ## Packed coordinate data -/

/-- First nonzero flat BOT target coordinate for each (3,1,c,d). -/
def targetBytesA3B1 : ℕ := 0x1020c010500090301040114010002010c0105012101000101040100030004040400220300070e0100130101050c01060a0000010c0206010301010401060100

/-! ## Kernel-checked law -/

/-- All 64 entries with first labels (3,1) are actual raw ratios. -/
theorem exactA3B1 : ∀ c d : ZMod 8,
    IsExactWitness 3 1 c d 0
      (packedByteAt targetBytesA3B1 (pairLeafIndex c d)) := by
  decide +kernel

end RealPChiCertificate
end Superfusion.RMod.RawDCT
