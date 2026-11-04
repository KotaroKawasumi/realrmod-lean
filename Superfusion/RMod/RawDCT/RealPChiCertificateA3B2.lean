import Superfusion.RMod.RawDCT.RealPChiCertificateCore

/-!
# Exact real pentagon certificate leaf: first labels (3,2)

The packed bytes are candidate target coordinates extracted by the existing
exact certgen BOT scan.  The theorem independently rechecks the actual
realTData.hom TOP/BOT coefficients with decide +kernel.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT
namespace RealPChiCertificate

/-! ## Packed coordinate data -/

/-- First nonzero flat BOT target coordinate for each (3,2,c,d). -/
def targetBytesA3B2 : ℕ := 0x1151300020105001500000601010d0101010b0b0500051506030806010100080200070403040306000604000101070604000504110602000001150806060000

/-! ## Kernel-checked law -/

/-- All 64 entries with first labels (3,2) are actual raw ratios. -/
theorem exactA3B2 : ∀ c d : ZMod 8,
    IsExactWitness 3 2 c d 0
      (packedByteAt targetBytesA3B2 (pairLeafIndex c d)) := by
  decide +kernel

end RealPChiCertificate
end Superfusion.RMod.RawDCT
