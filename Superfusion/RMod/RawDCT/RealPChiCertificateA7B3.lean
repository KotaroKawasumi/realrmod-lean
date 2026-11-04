import Superfusion.RMod.RawDCT.RealPChiCertificateCore

/-!
# Exact real pentagon certificate leaf: first labels (7,3)

The packed bytes are candidate target coordinates extracted by the existing
exact certgen BOT scan.  The theorem independently rechecks the actual
realTData.hom TOP/BOT coefficients with decide +kernel.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT
namespace RealPChiCertificate

/-! ## Packed coordinate data -/

/-- First nonzero flat BOT target coordinate for each (7,3,c,d). -/
def targetBytesA7B3 : ℕ := 0x1010102150102020101010501030100020124030001020100170112010404001e03010400010100000002030c0c0004000200040c0b0c010200010000040100

/-! ## Kernel-checked law -/

/-- All 64 entries with first labels (7,3) are actual raw ratios. -/
theorem exactA7B3 : ∀ c d : ZMod 8,
    IsExactWitness 7 3 c d 0
      (packedByteAt targetBytesA7B3 (pairLeafIndex c d)) := by
  decide +kernel

end RealPChiCertificate
end Superfusion.RMod.RawDCT
