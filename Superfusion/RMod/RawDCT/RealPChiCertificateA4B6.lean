import Superfusion.RMod.RawDCT.RealPChiCertificateCore

/-!
# Exact real pentagon certificate leaf: first labels (4,6)

The packed bytes are candidate target coordinates extracted by the existing
exact certgen BOT scan.  The theorem independently rechecks the actual
realTData.hom TOP/BOT coefficients with decide +kernel.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT
namespace RealPChiCertificate

/-! ## Packed coordinate data -/

/-- First nonzero flat BOT target coordinate for each (4,6,c,d). -/
def targetBytesA4B6 : ℕ := 0x6020a011102020000100101010300000404200300050000051007120506060a1a05010c000507000300000a0e1c0000000000061c0008040000000a00000400

/-! ## Kernel-checked law -/

/-- All 64 entries with first labels (4,6) are actual raw ratios. -/
theorem exactA4B6 : ∀ c d : ZMod 8,
    IsExactWitness 4 6 c d 0
      (packedByteAt targetBytesA4B6 (pairLeafIndex c d)) := by
  decide +kernel

end RealPChiCertificate
end Superfusion.RMod.RawDCT
