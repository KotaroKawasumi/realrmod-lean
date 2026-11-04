import Superfusion.RMod.RawDCT.RealPChiCertificateCore

/-!
# Exact real pentagon certificate leaf: first labels (6,2)

The packed bytes are candidate target coordinates extracted by the existing
exact certgen BOT scan.  The theorem independently rechecks the actual
realTData.hom TOP/BOT coefficients with decide +kernel.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT
namespace RealPChiCertificate

/-! ## Packed coordinate data -/

/-- First nonzero flat BOT target coordinate for each (6,2,c,d). -/
def targetBytesA6B2 : ℕ := 0x3000601000000000006010000000003060100000000030001000000000300060000000003000601000000030006010000000300060100000003000601000000

/-! ## Kernel-checked law -/

/-- All 64 entries with first labels (6,2) are actual raw ratios. -/
theorem exactA6B2 : ∀ c d : ZMod 8,
    IsExactWitness 6 2 c d 0
      (packedByteAt targetBytesA6B2 (pairLeafIndex c d)) := by
  decide +kernel

end RealPChiCertificate
end Superfusion.RMod.RawDCT
