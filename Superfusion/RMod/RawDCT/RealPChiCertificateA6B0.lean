import Superfusion.RMod.RawDCT.RealPChiCertificateCore

/-!
# Exact real pentagon certificate leaf: first labels (6,0)

The packed bytes are candidate target coordinates extracted by the existing
exact certgen BOT scan.  The theorem independently rechecks the actual
realTData.hom TOP/BOT coefficients with decide +kernel.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT
namespace RealPChiCertificate

/-! ## Packed coordinate data -/

/-- First nonzero flat BOT target coordinate for each (6,0,c,d). -/
def targetBytesA6B0 : ℕ := 0x2030000000000090101010105000002010001010400030103020c0a01000003000204010100000300060100000002000005010002000000000000000000

/-! ## Kernel-checked law -/

/-- All 64 entries with first labels (6,0) are actual raw ratios. -/
theorem exactA6B0 : ∀ c d : ZMod 8,
    IsExactWitness 6 0 c d 0
      (packedByteAt targetBytesA6B0 (pairLeafIndex c d)) := by
  decide +kernel

end RealPChiCertificate
end Superfusion.RMod.RawDCT
