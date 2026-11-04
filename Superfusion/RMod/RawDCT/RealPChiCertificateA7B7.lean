import Superfusion.RMod.RawDCT.RealPChiCertificateCore

/-!
# Exact real pentagon certificate leaf: first labels (7,7)

The packed bytes are candidate target coordinates extracted by the existing
exact certgen BOT scan.  The theorem independently rechecks the actual
realTData.hom TOP/BOT coefficients with decide +kernel.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT
namespace RealPChiCertificate

/-! ## Packed coordinate data -/

/-- First nonzero flat BOT target coordinate for each (7,7,c,d). -/
def targetBytesA7B7 : ℕ := 0x404000200000000040d0105010105040409040001010207020502020c0c050400020002000b0500000300010604000002000408030001000004070400000000

/-! ## Kernel-checked law -/

/-- All 64 entries with first labels (7,7) are actual raw ratios. -/
theorem exactA7B7 : ∀ c d : ZMod 8,
    IsExactWitness 7 7 c d 0
      (packedByteAt targetBytesA7B7 (pairLeafIndex c d)) := by
  decide +kernel

end RealPChiCertificate
end Superfusion.RMod.RawDCT
