import Superfusion.RMod.RawDCT.RealPChiCertificateCore

/-!
# Exact real pentagon certificate leaf: first labels (0,4)

The packed bytes are candidate target coordinates extracted by the existing
exact certgen BOT scan.  The theorem independently rechecks the actual
realTData.hom TOP/BOT coefficients with decide +kernel.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT
namespace RealPChiCertificate

/-! ## Packed coordinate data -/

/-- First nonzero flat BOT target coordinate for each (0,4,c,d). -/
def targetBytesA0B4 : ℕ := 0x40600000405000000000e00000400060003001102020000020600000602000202120009050400040b01000304000006050100040400000000000000000000

/-! ## Kernel-checked law -/

/-- All 64 entries with first labels (0,4) are actual raw ratios. -/
theorem exactA0B4 : ∀ c d : ZMod 8,
    IsExactWitness 0 4 c d 0
      (packedByteAt targetBytesA0B4 (pairLeafIndex c d)) := by
  decide +kernel

end RealPChiCertificate
end Superfusion.RMod.RawDCT
