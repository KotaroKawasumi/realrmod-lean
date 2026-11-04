import Superfusion.RMod.RawDCT.RealPChiCertificateCore

/-!
# Exact real pentagon certificate leaf: first labels (3,4)

The packed bytes are candidate target coordinates extracted by the existing
exact certgen BOT scan.  The theorem independently rechecks the actual
realTData.hom TOP/BOT coefficients with decide +kernel.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT
namespace RealPChiCertificate

/-! ## Packed coordinate data -/

/-- First nonzero flat BOT target coordinate for each (3,4,c,d). -/
def targetBytesA3B4 : ℕ := 0x80407000202000304030000020003080707010500000a0000011500001d0100010201000b0401040500010f0101000201000f05030201020308000004020200

/-! ## Kernel-checked law -/

/-- All 64 entries with first labels (3,4) are actual raw ratios. -/
theorem exactA3B4 : ∀ c d : ZMod 8,
    IsExactWitness 3 4 c d 0
      (packedByteAt targetBytesA3B4 (pairLeafIndex c d)) := by
  decide +kernel

end RealPChiCertificate
end Superfusion.RMod.RawDCT
