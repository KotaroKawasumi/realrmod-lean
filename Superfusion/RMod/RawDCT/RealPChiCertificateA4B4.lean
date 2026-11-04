import Superfusion.RMod.RawDCT.RealPChiCertificateCore

/-!
# Exact real pentagon certificate leaf: first labels (4,4)

The packed bytes are candidate target coordinates extracted by the existing
exact certgen BOT scan.  The theorem independently rechecks the actual
realTData.hom TOP/BOT coefficients with decide +kernel.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT
namespace RealPChiCertificate

/-! ## Packed coordinate data -/

/-- First nonzero flat BOT target coordinate for each (4,4,c,d). -/
def targetBytesA4B4 : ℕ := 0x2060000040200000600000402000002000004020000020600040200000206000402000002060000020000020600000400000206000004020002060000040200

/-! ## Kernel-checked law -/

/-- All 64 entries with first labels (4,4) are actual raw ratios. -/
theorem exactA4B4 : ∀ c d : ZMod 8,
    IsExactWitness 4 4 c d 0
      (packedByteAt targetBytesA4B4 (pairLeafIndex c d)) := by
  decide +kernel

end RealPChiCertificate
end Superfusion.RMod.RawDCT
