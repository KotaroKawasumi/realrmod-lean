import Superfusion.RMod.RawDCT.RealPChiCertificateCore

/-!
# Exact real pentagon certificate leaf: first labels (7,1)

The packed bytes are candidate target coordinates extracted by the existing
exact certgen BOT scan.  The theorem independently rechecks the actual
realTData.hom TOP/BOT coefficients with decide +kernel.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT
namespace RealPChiCertificate

/-! ## Packed coordinate data -/

/-- First nonzero flat BOT target coordinate for each (7,1,c,d). -/
def targetBytesA7B1 : ℕ := 0x10403000100010104030001000100040300010001000103000100010001040001000100010403010001000104030000010001040300010100010403000100

/-! ## Kernel-checked law -/

/-- All 64 entries with first labels (7,1) are actual raw ratios. -/
theorem exactA7B1 : ∀ c d : ZMod 8,
    IsExactWitness 7 1 c d 0
      (packedByteAt targetBytesA7B1 (pairLeafIndex c d)) := by
  decide +kernel

end RealPChiCertificate
end Superfusion.RMod.RawDCT
