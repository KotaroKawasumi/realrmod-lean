import Superfusion.RMod.RawDCT.RealPChiCertificateCore

/-!
# Exact real pentagon certificate leaf: first labels (1,7)

The packed bytes are candidate target coordinates extracted by the existing
exact certgen BOT scan.  The theorem independently rechecks the actual
realTData.hom TOP/BOT coefficients with decide +kernel.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT
namespace RealPChiCertificate

/-! ## Packed coordinate data -/

/-- First nonzero flat BOT target coordinate for each (1,7,c,d). -/
def targetBytesA1B7 : ℕ := 0x50401000100010504010001000100040100010001000501000100010005040001000100050401010001000504010000010005040100010100050401000100

/-! ## Kernel-checked law -/

/-- All 64 entries with first labels (1,7) are actual raw ratios. -/
theorem exactA1B7 : ∀ c d : ZMod 8,
    IsExactWitness 1 7 c d 0
      (packedByteAt targetBytesA1B7 (pairLeafIndex c d)) := by
  decide +kernel

end RealPChiCertificate
end Superfusion.RMod.RawDCT
