import Superfusion.RMod.RawDCT.RealPChiCertificateCore

/-!
# Exact real pentagon certificate leaf: first labels (0,2)

The packed bytes are candidate target coordinates extracted by the existing
exact certgen BOT scan.  The theorem independently rechecks the actual
realTData.hom TOP/BOT coefficients with decide +kernel.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT
namespace RealPChiCertificate

/-! ## Packed coordinate data -/

/-- First nonzero flat BOT target coordinate for each (0,2,c,d). -/
def targetBytesA0B2 : ℕ := 0x200010408000200000201000003000001041002000200000908030a020203000e01010700020200070000040504000000000003040005000000000000000000

/-! ## Kernel-checked law -/

/-- All 64 entries with first labels (0,2) are actual raw ratios. -/
theorem exactA0B2 : ∀ c d : ZMod 8,
    IsExactWitness 0 2 c d 0
      (packedByteAt targetBytesA0B2 (pairLeafIndex c d)) := by
  decide +kernel

end RealPChiCertificate
end Superfusion.RMod.RawDCT
