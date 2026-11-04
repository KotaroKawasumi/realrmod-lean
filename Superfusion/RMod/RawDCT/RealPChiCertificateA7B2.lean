import Superfusion.RMod.RawDCT.RealPChiCertificateCore

/-!
# Exact real pentagon certificate leaf: first labels (7,2)

The packed bytes are candidate target coordinates extracted by the existing
exact certgen BOT scan.  The theorem independently rechecks the actual
realTData.hom TOP/BOT coefficients with decide +kernel.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT
namespace RealPChiCertificate

/-! ## Packed coordinate data -/

/-- First nonzero flat BOT target coordinate for each (7,2,c,d). -/
def targetBytesA7B2 : ℕ := 0x1010104000101010002040000000000000401010101010100050008070100010001000202000000020001000001050100010000010001020100010100010200

/-! ## Kernel-checked law -/

/-- All 64 entries with first labels (7,2) are actual raw ratios. -/
theorem exactA7B2 : ∀ c d : ZMod 8,
    IsExactWitness 7 2 c d 0
      (packedByteAt targetBytesA7B2 (pairLeafIndex c d)) := by
  decide +kernel

end RealPChiCertificate
end Superfusion.RMod.RawDCT
