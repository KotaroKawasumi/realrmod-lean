import Superfusion.RMod.RawDCT.RealPChiCertificateCore

/-!
# Exact real pentagon certificate leaf: first labels (0,7)

The packed bytes are candidate target coordinates extracted by the existing
exact certgen BOT scan.  The theorem independently rechecks the actual
realTData.hom TOP/BOT coefficients with decide +kernel.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT
namespace RealPChiCertificate

/-! ## Packed coordinate data -/

/-- First nonzero flat BOT target coordinate for each (0,7,c,d). -/
def targetBytesA0B7 : ℕ := 0x40704000000000403010000000000070001040003010004030200030900000400010000080100020001010001020001000104030001000000000000000000

/-! ## Kernel-checked law -/

/-- All 64 entries with first labels (0,7) are actual raw ratios. -/
theorem exactA0B7 : ∀ c d : ZMod 8,
    IsExactWitness 0 7 c d 0
      (packedByteAt targetBytesA0B7 (pairLeafIndex c d)) := by
  decide +kernel

end RealPChiCertificate
end Superfusion.RMod.RawDCT
