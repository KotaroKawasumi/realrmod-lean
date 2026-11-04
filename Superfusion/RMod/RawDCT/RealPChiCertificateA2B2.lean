import Superfusion.RMod.RawDCT.RealPChiCertificateCore

/-!
# Exact real pentagon certificate leaf: first labels (2,2)

The packed bytes are candidate target coordinates extracted by the existing
exact certgen BOT scan.  The theorem independently rechecks the actual
realTData.hom TOP/BOT coefficients with decide +kernel.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT
namespace RealPChiCertificate

/-! ## Packed coordinate data -/

/-- First nonzero flat BOT target coordinate for each (2,2,c,d). -/
def targetBytesA2B2 : ℕ := 0x1040a140409070002010e0000030005100d00210301000a0c0600070903020c0222071101040a04130000020f0a0c0a01010004020c00070000020a0c0000

/-! ## Kernel-checked law -/

/-- All 64 entries with first labels (2,2) are actual raw ratios. -/
theorem exactA2B2 : ∀ c d : ZMod 8,
    IsExactWitness 2 2 c d 0
      (packedByteAt targetBytesA2B2 (pairLeafIndex c d)) := by
  decide +kernel

end RealPChiCertificate
end Superfusion.RMod.RawDCT
