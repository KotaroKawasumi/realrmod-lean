import Superfusion.RMod.RawDCT.RealPChiCertificateCore

/-!
# Exact real pentagon certificate leaf: first labels (2,1)

The packed bytes are candidate target coordinates extracted by the existing
exact certgen BOT scan.  The theorem independently rechecks the actual
realTData.hom TOP/BOT coefficients with decide +kernel.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT
namespace RealPChiCertificate

/-! ## Packed coordinate data -/

/-- First nonzero flat BOT target coordinate for each (2,1,c,d). -/
def targetBytesA2B1 : ℕ := 0x200020804000400000208000006000001000101070001000302040005030603041300030009000c06010905080209000301010202020b05000000030c000500

/-! ## Kernel-checked law -/

/-- All 64 entries with first labels (2,1) are actual raw ratios. -/
theorem exactA2B1 : ∀ c d : ZMod 8,
    IsExactWitness 2 1 c d 0
      (packedByteAt targetBytesA2B1 (pairLeafIndex c d)) := by
  decide +kernel

end RealPChiCertificate
end Superfusion.RMod.RawDCT
