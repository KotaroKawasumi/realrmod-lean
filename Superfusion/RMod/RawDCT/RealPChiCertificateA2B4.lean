import Superfusion.RMod.RawDCT.RealPChiCertificateCore

/-!
# Exact real pentagon certificate leaf: first labels (2,4)

The packed bytes are candidate target coordinates extracted by the existing
exact certgen BOT scan.  The theorem independently rechecks the actual
realTData.hom TOP/BOT coefficients with decide +kernel.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT
namespace RealPChiCertificate

/-! ## Packed coordinate data -/

/-- First nonzero flat BOT target coordinate for each (2,4,c,d). -/
def targetBytesA2B4 : ℕ := 0x40000060a030009001b050b00010c040900130101081403060b01021d1f020a0a01000b26010b03010309140109040602090506000302030904030a03060300

/-! ## Kernel-checked law -/

/-- All 64 entries with first labels (2,4) are actual raw ratios. -/
theorem exactA2B4 : ∀ c d : ZMod 8,
    IsExactWitness 2 4 c d 0
      (packedByteAt targetBytesA2B4 (pairLeafIndex c d)) := by
  decide +kernel

end RealPChiCertificate
end Superfusion.RMod.RawDCT
