import Superfusion.RMod.RawDCT.RealPChiCertificateCore

/-!
# Exact real pentagon certificate leaf: first labels (6,1)

The packed bytes are candidate target coordinates extracted by the existing
exact certgen BOT scan.  The theorem independently rechecks the actual
realTData.hom TOP/BOT coefficients with decide +kernel.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT
namespace RealPChiCertificate

/-! ## Packed coordinate data -/

/-- First nonzero flat BOT target coordinate for each (6,1,c,d). -/
def targetBytesA6B1 : ℕ := 0x40103000200020400000202000200010101000001020003010800010800050102010103070201000000020002030001010206000401020200000501000200

/-! ## Kernel-checked law -/

/-- All 64 entries with first labels (6,1) are actual raw ratios. -/
theorem exactA6B1 : ∀ c d : ZMod 8,
    IsExactWitness 6 1 c d 0
      (packedByteAt targetBytesA6B1 (pairLeafIndex c d)) := by
  decide +kernel

end RealPChiCertificate
end Superfusion.RMod.RawDCT
