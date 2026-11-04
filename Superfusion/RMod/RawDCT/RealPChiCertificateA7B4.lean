import Superfusion.RMod.RawDCT.RealPChiCertificateCore

/-!
# Exact real pentagon certificate leaf: first labels (7,4)

The packed bytes are candidate target coordinates extracted by the existing
exact certgen BOT scan.  The theorem independently rechecks the actual
realTData.hom TOP/BOT coefficients with decide +kernel.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT
namespace RealPChiCertificate

/-! ## Packed coordinate data -/

/-- First nonzero flat BOT target coordinate for each (7,4,c,d). -/
def targetBytesA7B4 : ℕ := 0x1020904040400010300040601020000020407010005000403000006020002160004050803030001110e0107040903030301010101000402050003090000

/-! ## Kernel-checked law -/

/-- All 64 entries with first labels (7,4) are actual raw ratios. -/
theorem exactA7B4 : ∀ c d : ZMod 8,
    IsExactWitness 7 4 c d 0
      (packedByteAt targetBytesA7B4 (pairLeafIndex c d)) := by
  decide +kernel

end RealPChiCertificate
end Superfusion.RMod.RawDCT
