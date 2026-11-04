import Superfusion.RMod.RawDCT.RealPChiCertificateCore

/-!
# Exact real pentagon certificate leaf: first labels (0,5)

The packed bytes are candidate target coordinates extracted by the existing
exact certgen BOT scan.  The theorem independently rechecks the actual
realTData.hom TOP/BOT coefficients with decide +kernel.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT
namespace RealPChiCertificate

/-! ## Packed coordinate data -/

/-- First nonzero flat BOT target coordinate for each (0,5,c,d). -/
def targetBytesA0B5 : ℕ := 0x8060101050000010a0001010d00000800100500040001020506000001000100071201070000000610010002000004000104010004000000000000000000

/-! ## Kernel-checked law -/

/-- All 64 entries with first labels (0,5) are actual raw ratios. -/
theorem exactA0B5 : ∀ c d : ZMod 8,
    IsExactWitness 0 5 c d 0
      (packedByteAt targetBytesA0B5 (pairLeafIndex c d)) := by
  decide +kernel

end RealPChiCertificate
end Superfusion.RMod.RawDCT
