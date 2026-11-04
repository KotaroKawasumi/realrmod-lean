import Superfusion.RMod.RawDCT.RealPChiCertificateCore

/-!
# Exact real pentagon certificate leaf: first labels (1,0)

The packed bytes are candidate target coordinates extracted by the existing
exact certgen BOT scan.  The theorem independently rechecks the actual
realTData.hom TOP/BOT coefficients with decide +kernel.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT
namespace RealPChiCertificate

/-! ## Packed coordinate data -/

/-- First nonzero flat BOT target coordinate for each (1,0,c,d). -/
def targetBytesA1B0 : ℕ := 0x1000504010001000203040101000100010400000100020000010104070204000700000300020700000000000100050000000004030000000000000000000000

/-! ## Kernel-checked law -/

/-- All 64 entries with first labels (1,0) are actual raw ratios. -/
theorem exactA1B0 : ∀ c d : ZMod 8,
    IsExactWitness 1 0 c d 0
      (packedByteAt targetBytesA1B0 (pairLeafIndex c d)) := by
  decide +kernel

end RealPChiCertificate
end Superfusion.RMod.RawDCT
