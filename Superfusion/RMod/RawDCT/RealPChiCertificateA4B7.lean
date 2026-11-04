import Superfusion.RMod.RawDCT.RealPChiCertificateCore

/-!
# Exact real pentagon certificate leaf: first labels (4,7)

The packed bytes are candidate target coordinates extracted by the existing
exact certgen BOT scan.  The theorem independently rechecks the actual
realTData.hom TOP/BOT coefficients with decide +kernel.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT
namespace RealPChiCertificate

/-! ## Packed coordinate data -/

/-- First nonzero flat BOT target coordinate for each (4,7,c,d). -/
def targetBytesA4B7 : ℕ := 0x4010100000400040100010006000400000001070000060000100004010400031b0003030004000a01150900060c0403010500010103050004060000040500

/-! ## Kernel-checked law -/

/-- All 64 entries with first labels (4,7) are actual raw ratios. -/
theorem exactA4B7 : ∀ c d : ZMod 8,
    IsExactWitness 4 7 c d 0
      (packedByteAt targetBytesA4B7 (pairLeafIndex c d)) := by
  decide +kernel

end RealPChiCertificate
end Superfusion.RMod.RawDCT
