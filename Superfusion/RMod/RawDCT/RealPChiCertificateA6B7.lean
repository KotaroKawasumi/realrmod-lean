import Superfusion.RMod.RawDCT.RealPChiCertificateCore

/-!
# Exact real pentagon certificate leaf: first labels (6,7)

The packed bytes are candidate target coordinates extracted by the existing
exact certgen BOT scan.  The theorem independently rechecks the actual
realTData.hom TOP/BOT coefficients with decide +kernel.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT
namespace RealPChiCertificate

/-! ## Packed coordinate data -/

/-- First nonzero flat BOT target coordinate for each (6,7,c,d). -/
def targetBytesA6B7 : ℕ := 0x200040101050002050700010109000102001005000402010305060000050301000706010c0300000604020106000004000808020002000000020300000000

/-! ## Kernel-checked law -/

/-- All 64 entries with first labels (6,7) are actual raw ratios. -/
theorem exactA6B7 : ∀ c d : ZMod 8,
    IsExactWitness 6 7 c d 0
      (packedByteAt targetBytesA6B7 (pairLeafIndex c d)) := by
  decide +kernel

end RealPChiCertificate
end Superfusion.RMod.RawDCT
