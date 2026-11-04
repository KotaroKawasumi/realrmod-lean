import Superfusion.RMod.RawDCT.RealPChiCertificateCore

/-!
# Exact real pentagon certificate leaf: first labels (2,0)

The packed bytes are candidate target coordinates extracted by the existing
exact certgen BOT scan.  The theorem independently rechecks the actual
realTData.hom TOP/BOT coefficients with decide +kernel.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT
namespace RealPChiCertificate

/-! ## Packed coordinate data -/

/-- First nonzero flat BOT target coordinate for each (2,0,c,d). -/
def targetBytesA2B0 : ℕ := 0x200010404000200000201000003000001040402000300000904030a030603000a01010600020200070000020a0c0000000000030c0005000000000000000000

/-! ## Kernel-checked law -/

/-- All 64 entries with first labels (2,0) are actual raw ratios. -/
theorem exactA2B0 : ∀ c d : ZMod 8,
    IsExactWitness 2 0 c d 0
      (packedByteAt targetBytesA2B0 (pairLeafIndex c d)) := by
  decide +kernel

end RealPChiCertificate
end Superfusion.RMod.RawDCT
