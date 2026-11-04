import Superfusion.RMod.RawDCT.RealPChiCertificateCore

/-!
# Exact real pentagon certificate leaf: first labels (5,7)

The packed bytes are candidate target coordinates extracted by the existing
exact certgen BOT scan.  The theorem independently rechecks the actual
realTData.hom TOP/BOT coefficients with decide +kernel.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT
namespace RealPChiCertificate

/-! ## Packed coordinate data -/

/-- First nonzero flat BOT target coordinate for each (5,7,c,d). -/
def targetBytesA5B7 : ℕ := 0xc01010109000406040c050004000d0302052102020401030000000803060301220008070c0101130100020f01010a0501040c0501050000040601010500

/-! ## Kernel-checked law -/

/-- All 64 entries with first labels (5,7) are actual raw ratios. -/
theorem exactA5B7 : ∀ c d : ZMod 8,
    IsExactWitness 5 7 c d 0
      (packedByteAt targetBytesA5B7 (pairLeafIndex c d)) := by
  decide +kernel

end RealPChiCertificate
end Superfusion.RMod.RawDCT
