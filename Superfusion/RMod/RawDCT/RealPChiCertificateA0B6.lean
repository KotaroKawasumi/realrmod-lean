import Superfusion.RMod.RawDCT.RealPChiCertificateCore

/-!
# Exact real pentagon certificate leaf: first labels (0,6)

The packed bytes are candidate target coordinates extracted by the existing
exact certgen BOT scan.  The theorem independently rechecks the actual
realTData.hom TOP/BOT coefficients with decide +kernel.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT
namespace RealPChiCertificate

/-! ## Packed coordinate data -/

/-- First nonzero flat BOT target coordinate for each (0,6,c,d). -/
def targetBytesA0B6 : ℕ := 0x20300000000000d0101010105000002010001010800030102020c0e010000020002100101000003000a0100000002000005010002000000000000000000

/-! ## Kernel-checked law -/

/-- All 64 entries with first labels (0,6) are actual raw ratios. -/
theorem exactA0B6 : ∀ c d : ZMod 8,
    IsExactWitness 0 6 c d 0
      (packedByteAt targetBytesA0B6 (pairLeafIndex c d)) := by
  decide +kernel

end RealPChiCertificate
end Superfusion.RMod.RawDCT
