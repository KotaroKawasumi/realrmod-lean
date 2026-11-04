import Superfusion.RMod.RawDCT.RealPChiCertificateCore

/-!
# Exact real pentagon certificate leaf: first labels (1,6)

The packed bytes are candidate target coordinates extracted by the existing
exact certgen BOT scan.  The theorem independently rechecks the actual
realTData.hom TOP/BOT coefficients with decide +kernel.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT
namespace RealPChiCertificate

/-! ## Packed coordinate data -/

/-- First nonzero flat BOT target coordinate for each (1,6,c,d). -/
def targetBytesA1B6 : ℕ := 0x30c0003000100020c01030201000203000201000001040403010500010d0501010101010514000100000001070000000101010c010101010203040101000100

/-! ## Kernel-checked law -/

/-- All 64 entries with first labels (1,6) are actual raw ratios. -/
theorem exactA1B6 : ∀ c d : ZMod 8,
    IsExactWitness 1 6 c d 0
      (packedByteAt targetBytesA1B6 (pairLeafIndex c d)) := by
  decide +kernel

end RealPChiCertificate
end Superfusion.RMod.RawDCT
