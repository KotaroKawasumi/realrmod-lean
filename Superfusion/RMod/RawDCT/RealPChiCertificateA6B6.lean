import Superfusion.RMod.RawDCT.RealPChiCertificateCore

/-!
# Exact real pentagon certificate leaf: first labels (6,6)

The packed bytes are candidate target coordinates extracted by the existing
exact certgen BOT scan.  The theorem independently rechecks the actual
realTData.hom TOP/BOT coefficients with decide +kernel.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT
namespace RealPChiCertificate

/-! ## Packed coordinate data -/

/-- First nonzero flat BOT target coordinate for each (6,6,c,d). -/
def targetBytesA6B6 : ℕ := 0x9000601010109000101021b0500040906020205210109010103000000040101030122000400070101130111000c01010a051001070301050009010101010500

/-! ## Kernel-checked law -/

/-- All 64 entries with first labels (6,6) are actual raw ratios. -/
theorem exactA6B6 : ∀ c d : ZMod 8,
    IsExactWitness 6 6 c d 0
      (packedByteAt targetBytesA6B6 (pairLeafIndex c d)) := by
  decide +kernel

end RealPChiCertificate
end Superfusion.RMod.RawDCT
