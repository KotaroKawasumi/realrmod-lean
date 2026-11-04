import Superfusion.RMod.RawDCT.RealPChiCertificateCore

/-!
# Exact real pentagon certificate leaf: first labels (7,5)

The packed bytes are candidate target coordinates extracted by the existing
exact certgen BOT scan.  The theorem independently rechecks the actual
realTData.hom TOP/BOT coefficients with decide +kernel.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT
namespace RealPChiCertificate

/-! ## Packed coordinate data -/

/-- First nonzero flat BOT target coordinate for each (7,5,c,d). -/
def targetBytesA7B5 : ℕ := 0x6000000090701010008010003000f000001210301010001010007040101010522070700040000130000000400030a010101040103010700010100030100

/-! ## Kernel-checked law -/

/-- All 64 entries with first labels (7,5) are actual raw ratios. -/
theorem exactA7B5 : ∀ c d : ZMod 8,
    IsExactWitness 7 5 c d 0
      (packedByteAt targetBytesA7B5 (pairLeafIndex c d)) := by
  decide +kernel

end RealPChiCertificate
end Superfusion.RMod.RawDCT
