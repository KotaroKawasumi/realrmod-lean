import Superfusion.RMod.RawDCT.RealPChiCertificateCore

/-!
# Exact real pentagon certificate leaf: first labels (4,3)

The packed bytes are candidate target coordinates extracted by the existing
exact certgen BOT scan.  The theorem independently rechecks the actual
realTData.hom TOP/BOT coefficients with decide +kernel.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT
namespace RealPChiCertificate

/-! ## Packed coordinate data -/

/-- First nonzero flat BOT target coordinate for each (4,3,c,d). -/
def targetBytesA4B3 : ℕ := 0x2000706060800020003050310000202070402010001031206021900011210000210010102020104010000032001050601010303030402040202120004060400

/-! ## Kernel-checked law -/

/-- All 64 entries with first labels (4,3) are actual raw ratios. -/
theorem exactA4B3 : ∀ c d : ZMod 8,
    IsExactWitness 4 3 c d 0
      (packedByteAt targetBytesA4B3 (pairLeafIndex c d)) := by
  decide +kernel

end RealPChiCertificate
end Superfusion.RMod.RawDCT
