import Superfusion.RMod.RawDCT.RealPChiCertificateCore

/-!
# Exact real pentagon certificate leaf: first labels (7,0)

The packed bytes are candidate target coordinates extracted by the existing
exact certgen BOT scan.  The theorem independently rechecks the actual
realTData.hom TOP/BOT coefficients with decide +kernel.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT
namespace RealPChiCertificate

/-! ## Packed coordinate data -/

/-- First nonzero flat BOT target coordinate for each (7,0,c,d). -/
def targetBytesA7B0 : ℕ := 0x40704000000000403010000000000070001010003010004020500030900000200010000040100010001010001020001000104030001000000000000000000

/-! ## Kernel-checked law -/

/-- All 64 entries with first labels (7,0) are actual raw ratios. -/
theorem exactA7B0 : ∀ c d : ZMod 8,
    IsExactWitness 7 0 c d 0
      (packedByteAt targetBytesA7B0 (pairLeafIndex c d)) := by
  decide +kernel

end RealPChiCertificate
end Superfusion.RMod.RawDCT
