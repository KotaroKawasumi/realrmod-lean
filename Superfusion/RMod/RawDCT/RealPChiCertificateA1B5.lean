import Superfusion.RMod.RawDCT.RealPChiCertificateCore

/-!
# Exact real pentagon certificate leaf: first labels (1,5)

The packed bytes are candidate target coordinates extracted by the existing
exact certgen BOT scan.  The theorem independently rechecks the actual
realTData.hom TOP/BOT coefficients with decide +kernel.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT
namespace RealPChiCertificate

/-! ## Packed coordinate data -/

/-- First nonzero flat BOT target coordinate for each (1,5,c,d). -/
def targetBytesA1B5 : ℕ := 0x40001000002000100080200000104040001000101000100000001020d0802000201000300010101010301000100010002010506020101020104000001000200

/-! ## Kernel-checked law -/

/-- All 64 entries with first labels (1,5) are actual raw ratios. -/
theorem exactA1B5 : ∀ c d : ZMod 8,
    IsExactWitness 1 5 c d 0
      (packedByteAt targetBytesA1B5 (pairLeafIndex c d)) := by
  decide +kernel

end RealPChiCertificate
end Superfusion.RMod.RawDCT
