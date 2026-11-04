import Superfusion.RMod.RawDCT.RealPChiCertificateCore

/-!
# Exact real pentagon certificate leaf: first labels (1,3)

The packed bytes are candidate target coordinates extracted by the existing
exact certgen BOT scan.  The theorem independently rechecks the actual
realTData.hom TOP/BOT coefficients with decide +kernel.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT
namespace RealPChiCertificate

/-! ## Packed coordinate data -/

/-- First nonzero flat BOT target coordinate for each (1,3,c,d). -/
def targetBytesA1B3 : ℕ := 0x10400010309070003000c07000300040001072103010000000100070902030003220711010f0003130000030400020a010100040602070700000300020700

/-! ## Kernel-checked law -/

/-- All 64 entries with first labels (1,3) are actual raw ratios. -/
theorem exactA1B3 : ∀ c d : ZMod 8,
    IsExactWitness 1 3 c d 0
      (packedByteAt targetBytesA1B3 (pairLeafIndex c d)) := by
  decide +kernel

end RealPChiCertificate
end Superfusion.RMod.RawDCT
