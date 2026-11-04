import Superfusion.RMod.RawDCT.RealPChiCertificateCore

/-!
# Exact real pentagon certificate leaf: first labels (0,1)

The packed bytes are candidate target coordinates extracted by the existing
exact certgen BOT scan.  The theorem independently rechecks the actual
realTData.hom TOP/BOT coefficients with decide +kernel.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT
namespace RealPChiCertificate

/-! ## Packed coordinate data -/

/-- First nonzero flat BOT target coordinate for each (0,1,c,d). -/
def targetBytesA0B1 : ℕ := 0x1000504010001000203080101000200010800000100040000010104030304000700000500020700000000000100050000000004030000000000000000000000

/-! ## Kernel-checked law -/

/-- All 64 entries with first labels (0,1) are actual raw ratios. -/
theorem exactA0B1 : ∀ c d : ZMod 8,
    IsExactWitness 0 1 c d 0
      (packedByteAt targetBytesA0B1 (pairLeafIndex c d)) := by
  decide +kernel

end RealPChiCertificate
end Superfusion.RMod.RawDCT
