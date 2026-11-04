import Superfusion.RMod.RawDCT.RealPChiCertificateCore

/-!
# Exact real pentagon certificate leaf: first labels (0,0)

The packed bytes are candidate target coordinates extracted by the existing
exact certgen BOT scan.  The theorem independently rechecks the actual
realTData.hom TOP/BOT coefficients with decide +kernel.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT
namespace RealPChiCertificate

/-! ## Packed coordinate data -/

/-- First nonzero flat BOT target coordinate for each (0,0,c,d). -/
def targetBytesA0B0 : ℕ := 0x0

/-! ## Kernel-checked law -/

/-- All 64 entries with first labels (0,0) are actual raw ratios. -/
theorem exactA0B0 : ∀ c d : ZMod 8,
    IsExactWitness 0 0 c d 0
      (packedByteAt targetBytesA0B0 (pairLeafIndex c d)) := by
  decide +kernel

end RealPChiCertificate
end Superfusion.RMod.RawDCT
