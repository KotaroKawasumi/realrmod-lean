import Superfusion.RMod.RawDCT.RealPChiCertificateCore

/-!
# Exact real pentagon certificate leaf: first labels (3,0)

The packed bytes are candidate target coordinates extracted by the existing
exact certgen BOT scan.  The theorem independently rechecks the actual
realTData.hom TOP/BOT coefficients with decide +kernel.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT
namespace RealPChiCertificate

/-! ## Packed coordinate data -/

/-- First nonzero flat BOT target coordinate for each (3,0,c,d). -/
def targetBytesA3B0 : ℕ := 0x4000101040404000001000006060000000008050700010003080000040202000414000300070400000115080606000003010104010601000000000000000000

/-! ## Kernel-checked law -/

/-- All 64 entries with first labels (3,0) are actual raw ratios. -/
theorem exactA3B0 : ∀ c d : ZMod 8,
    IsExactWitness 3 0 c d 0
      (packedByteAt targetBytesA3B0 (pairLeafIndex c d)) := by
  decide +kernel

end RealPChiCertificate
end Superfusion.RMod.RawDCT
