import Superfusion.RMod.RawDCT.RealPChiCertificateCore

/-!
# Exact real pentagon certificate leaf: first labels (6,3)

The packed bytes are candidate target coordinates extracted by the existing
exact certgen BOT scan.  The theorem independently rechecks the actual
realTData.hom TOP/BOT coefficients with decide +kernel.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT
namespace RealPChiCertificate

/-! ## Packed coordinate data -/

/-- First nonzero flat BOT target coordinate for each (6,3,c,d). -/
def targetBytesA6B3 : ℕ := 0x10301000501010002040005000002030300020101000100040000100c0102020301000600010004010000000601000100000302010401010003000204010100

/-! ## Kernel-checked law -/

/-- All 64 entries with first labels (6,3) are actual raw ratios. -/
theorem exactA6B3 : ∀ c d : ZMod 8,
    IsExactWitness 6 3 c d 0
      (packedByteAt targetBytesA6B3 (pairLeafIndex c d)) := by
  decide +kernel

end RealPChiCertificate
end Superfusion.RMod.RawDCT
