import Superfusion.RMod.RawDCT.RealPChiCertificateCore

/-!
# Exact real pentagon certificate leaf: first labels (7,6)

The packed bytes are candidate target coordinates extracted by the existing
exact certgen BOT scan.  The theorem independently rechecks the actual
realTData.hom TOP/BOT coefficients with decide +kernel.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT
namespace RealPChiCertificate

/-! ## Packed coordinate data -/

/-- First nonzero flat BOT target coordinate for each (7,6,c,d). -/
def targetBytesA7B6 : ℕ := 0x30101030101050401010a0001010c03030100100504010105020506040003000100070001010000000600160100000004040401010004000403010000000000

/-! ## Kernel-checked law -/

/-- All 64 entries with first labels (7,6) are actual raw ratios. -/
theorem exactA7B6 : ∀ c d : ZMod 8,
    IsExactWitness 7 6 c d 0
      (packedByteAt targetBytesA7B6 (pairLeafIndex c d)) := by
  decide +kernel

end RealPChiCertificate
end Superfusion.RMod.RawDCT
