import Superfusion.RMod.RawDCT.RealPChiCertificateCore

/-!
# Exact real pentagon certificate leaf: first labels (1,2)

The packed bytes are candidate target coordinates extracted by the existing
exact certgen BOT scan.  The theorem independently rechecks the actual
realTData.hom TOP/BOT coefficients with decide +kernel.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT
namespace RealPChiCertificate

/-! ## Packed coordinate data -/

/-- First nonzero flat BOT target coordinate for each (1,2,c,d). -/
def targetBytesA1B2 : ℕ := 0x4000100040004000002010000060000030101010700010001010400050207000213000300030101060109070301070003010101010004050000000001000500

/-! ## Kernel-checked law -/

/-- All 64 entries with first labels (1,2) are actual raw ratios. -/
theorem exactA1B2 : ∀ c d : ZMod 8,
    IsExactWitness 1 2 c d 0
      (packedByteAt targetBytesA1B2 (pairLeafIndex c d)) := by
  decide +kernel

end RealPChiCertificate
end Superfusion.RMod.RawDCT
