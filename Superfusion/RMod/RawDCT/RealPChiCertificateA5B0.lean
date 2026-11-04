import Superfusion.RMod.RawDCT.RealPChiCertificateCore

/-!
# Exact real pentagon certificate leaf: first labels (5,0)

The packed bytes are candidate target coordinates extracted by the existing
exact certgen BOT scan.  The theorem independently rechecks the actual
realTData.hom TOP/BOT coefficients with decide +kernel.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT
namespace RealPChiCertificate

/-! ## Packed coordinate data -/

/-- First nonzero flat BOT target coordinate for each (5,0,c,d). -/
def targetBytesA5B0 : ℕ := 0x406010105000001060001010900000400040500040001020406000001000100070601070000000604010002000004000104010004000000000000000000

/-! ## Kernel-checked law -/

/-- All 64 entries with first labels (5,0) are actual raw ratios. -/
theorem exactA5B0 : ∀ c d : ZMod 8,
    IsExactWitness 5 0 c d 0
      (packedByteAt targetBytesA5B0 (pairLeafIndex c d)) := by
  decide +kernel

end RealPChiCertificate
end Superfusion.RMod.RawDCT
