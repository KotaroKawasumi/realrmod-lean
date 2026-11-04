import Superfusion.RMod.RawDCT.RealPChiCertificateCore

/-!
# Exact real pentagon certificate leaf: first labels (4,5)

The packed bytes are candidate target coordinates extracted by the existing
exact certgen BOT scan.  The theorem independently rechecks the actual
realTData.hom TOP/BOT coefficients with decide +kernel.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT
namespace RealPChiCertificate

/-! ## Packed coordinate data -/

/-- First nonzero flat BOT target coordinate for each (4,5,c,d). -/
def targetBytesA4B5 : ℕ := 0xa0d05010301010601030103000000000100010101120103100300101c01010003010004000107110200121301000002000a0001031102020600030011020200

/-! ## Kernel-checked law -/

/-- All 64 entries with first labels (4,5) are actual raw ratios. -/
theorem exactA4B5 : ∀ c d : ZMod 8,
    IsExactWitness 4 5 c d 0
      (packedByteAt targetBytesA4B5 (pairLeafIndex c d)) := by
  decide +kernel

end RealPChiCertificate
end Superfusion.RMod.RawDCT
