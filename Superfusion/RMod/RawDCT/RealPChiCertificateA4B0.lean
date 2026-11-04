import Superfusion.RMod.RawDCT.RealPChiCertificateCore

/-!
# Exact real pentagon certificate leaf: first labels (4,0)

The packed bytes are candidate target coordinates extracted by the existing
exact certgen BOT scan.  The theorem independently rechecks the actual
realTData.hom TOP/BOT coefficients with decide +kernel.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT
namespace RealPChiCertificate

/-! ## Packed coordinate data -/

/-- First nonzero flat BOT target coordinate for each (4,0,c,d). -/
def targetBytesA4B0 : ℕ := 0x40600000405000000000a00000400060003001102020000020600000402000202120004060400040b01000304000006050100040400000000000000000000

/-! ## Kernel-checked law -/

/-- All 64 entries with first labels (4,0) are actual raw ratios. -/
theorem exactA4B0 : ∀ c d : ZMod 8,
    IsExactWitness 4 0 c d 0
      (packedByteAt targetBytesA4B0 (pairLeafIndex c d)) := by
  decide +kernel

end RealPChiCertificate
end Superfusion.RMod.RawDCT
