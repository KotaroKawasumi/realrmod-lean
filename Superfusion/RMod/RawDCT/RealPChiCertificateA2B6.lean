import Superfusion.RMod.RawDCT.RealPChiCertificateCore

/-!
# Exact real pentagon certificate leaf: first labels (2,6)

The packed bytes are candidate target coordinates extracted by the existing
exact certgen BOT scan.  The theorem independently rechecks the actual
realTData.hom TOP/BOT coefficients with decide +kernel.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT
namespace RealPChiCertificate

/-! ## Packed coordinate data -/

/-- First nonzero flat BOT target coordinate for each (2,6,c,d). -/
def targetBytesA2B6 : ℕ := 0x2010000030000000100000300000002000003000000020100030000000201000300000002010000000000020100000300000201000003000002010000030000

/-! ## Kernel-checked law -/

/-- All 64 entries with first labels (2,6) are actual raw ratios. -/
theorem exactA2B6 : ∀ c d : ZMod 8,
    IsExactWitness 2 6 c d 0
      (packedByteAt targetBytesA2B6 (pairLeafIndex c d)) := by
  decide +kernel

end RealPChiCertificate
end Superfusion.RMod.RawDCT
