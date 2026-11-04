import Superfusion.RMod.RawDCT.RealPChiCertificateCore

/-!
# Exact real pentagon certificate leaf: first labels (4,1)

The packed bytes are candidate target coordinates extracted by the existing
exact certgen BOT scan.  The theorem independently rechecks the actual
realTData.hom TOP/BOT coefficients with decide +kernel.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT
namespace RealPChiCertificate

/-! ## Packed coordinate data -/

/-- First nonzero flat BOT target coordinate for each (4,1,c,d). -/
def targetBytesA4B1 : ℕ := 0x50104000201050601010001010104050001010405130101050104061000000000000703011300040006000109020504040b0108010400000605010004040000

/-! ## Kernel-checked law -/

/-- All 64 entries with first labels (4,1) are actual raw ratios. -/
theorem exactA4B1 : ∀ c d : ZMod 8,
    IsExactWitness 4 1 c d 0
      (packedByteAt targetBytesA4B1 (pairLeafIndex c d)) := by
  decide +kernel

end RealPChiCertificate
end Superfusion.RMod.RawDCT
