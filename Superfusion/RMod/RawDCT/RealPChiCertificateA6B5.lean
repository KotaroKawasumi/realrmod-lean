import Superfusion.RMod.RawDCT.RealPChiCertificateCore

/-!
# Exact real pentagon certificate leaf: first labels (6,5)

The packed bytes are candidate target coordinates extracted by the existing
exact certgen BOT scan.  The theorem independently rechecks the actual
realTData.hom TOP/BOT coefficients with decide +kernel.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT
namespace RealPChiCertificate

/-! ## Packed coordinate data -/

/-- First nonzero flat BOT target coordinate for each (6,5,c,d). -/
def targetBytesA6B5 : ℕ := 0x1000900030104000001010101060002000500000703010101000400070001000316000000020101060114090205090103010309010006040002010001010400

/-! ## Kernel-checked law -/

/-- All 64 entries with first labels (6,5) are actual raw ratios. -/
theorem exactA6B5 : ∀ c d : ZMod 8,
    IsExactWitness 6 5 c d 0
      (packedByteAt targetBytesA6B5 (pairLeafIndex c d)) := by
  decide +kernel

end RealPChiCertificate
end Superfusion.RMod.RawDCT
