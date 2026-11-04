import Superfusion.RMod.RawDCT.RealPChiCertificateCore

/-!
# Exact real pentagon certificate leaf: first labels (1,1)

The packed bytes are candidate target coordinates extracted by the existing
exact certgen BOT scan.  The theorem independently rechecks the actual
realTData.hom TOP/BOT coefficients with decide +kernel.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT
namespace RealPChiCertificate

/-! ## Packed coordinate data -/

/-- First nonzero flat BOT target coordinate for each (1,1,c,d). -/
def targetBytesA1B1 : ℕ := 0x100050804000200000509000003000003010402000200000304030a020702040a01010700030003070000010608030000000002080005000000000403000000

/-! ## Kernel-checked law -/

/-- All 64 entries with first labels (1,1) are actual raw ratios. -/
theorem exactA1B1 : ∀ c d : ZMod 8,
    IsExactWitness 1 1 c d 0
      (packedByteAt targetBytesA1B1 (pairLeafIndex c d)) := by
  decide +kernel

end RealPChiCertificate
end Superfusion.RMod.RawDCT
