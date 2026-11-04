import Superfusion.RMod.RawDCT.RealPChiCertificateCore

/-!
# Exact real pentagon certificate leaf: first labels (4,2)

The packed bytes are candidate target coordinates extracted by the existing
exact certgen BOT scan.  The theorem independently rechecks the actual
realTData.hom TOP/BOT coefficients with decide +kernel.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT
namespace RealPChiCertificate

/-! ## Packed coordinate data -/

/-- First nonzero flat BOT target coordinate for each (4,2,c,d). -/
def targetBytesA4B2 : ℕ := 0xb01020b08000004011913080101010b00031000010300010b0805020808000009050003000301030003010300000a040202120101030000040b010003040000

/-! ## Kernel-checked law -/

/-- All 64 entries with first labels (4,2) are actual raw ratios. -/
theorem exactA4B2 : ∀ c d : ZMod 8,
    IsExactWitness 4 2 c d 0
      (packedByteAt targetBytesA4B2 (pairLeafIndex c d)) := by
  decide +kernel

end RealPChiCertificate
end Superfusion.RMod.RawDCT
