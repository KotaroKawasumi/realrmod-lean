import Superfusion.RMod.RawDCT.RealPChiCertificateCore

/-!
# Exact real pentagon certificate leaf: first labels (2,3)

The packed bytes are candidate target coordinates extracted by the existing
exact certgen BOT scan.  The theorem independently rechecks the actual
realTData.hom TOP/BOT coefficients with decide +kernel.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT
namespace RealPChiCertificate

/-! ## Packed coordinate data -/

/-- First nonzero flat BOT target coordinate for each (2,3,c,d). -/
def targetBytesA2B3 : ℕ := 0x10104080103050a0100100200010801021008210523050100000806200103060101070300110100020600030a02000204130018070501020a01010600020200

/-! ## Kernel-checked law -/

/-- All 64 entries with first labels (2,3) are actual raw ratios. -/
theorem exactA2B3 : ∀ c d : ZMod 8,
    IsExactWitness 2 3 c d 0
      (packedByteAt targetBytesA2B3 (pairLeafIndex c d)) := by
  decide +kernel

end RealPChiCertificate
end Superfusion.RMod.RawDCT
