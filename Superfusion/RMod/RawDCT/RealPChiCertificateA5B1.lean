import Superfusion.RMod.RawDCT.RealPChiCertificateCore

/-!
# Exact real pentagon certificate leaf: first labels (5,1)

The packed bytes are candidate target coordinates extracted by the existing
exact certgen BOT scan.  The theorem independently rechecks the actual
realTData.hom TOP/BOT coefficients with decide +kernel.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT
namespace RealPChiCertificate

/-! ## Packed coordinate data -/

/-- First nonzero flat BOT target coordinate for each (5,1,c,d). -/
def targetBytesA5B1 : ℕ := 0x40502000400040415000000010100040400010103050102000102080d05040101000304050501010301060504010002020101060104040400010401000400

/-! ## Kernel-checked law -/

/-- All 64 entries with first labels (5,1) are actual raw ratios. -/
theorem exactA5B1 : ∀ c d : ZMod 8,
    IsExactWitness 5 1 c d 0
      (packedByteAt targetBytesA5B1 (pairLeafIndex c d)) := by
  decide +kernel

end RealPChiCertificate
end Superfusion.RMod.RawDCT
