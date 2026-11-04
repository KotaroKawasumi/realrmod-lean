import Superfusion.RMod.RawDCT.RealPChiCertificateCore

/-!
# Exact real pentagon certificate leaf: first labels (1,4)

The packed bytes are candidate target coordinates extracted by the existing
exact certgen BOT scan.  The theorem independently rechecks the actual
realTData.hom TOP/BOT coefficients with decide +kernel.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT
namespace RealPChiCertificate

/-! ## Packed coordinate data -/

/-- First nonzero flat BOT target coordinate for each (1,4,c,d). -/
def targetBytesA1B4 : ℕ := 0x1010703040505000101030606010901000101030501000102060006010400040402070403010207010604000100000204010002050000040001010407020400

/-! ## Kernel-checked law -/

/-- All 64 entries with first labels (1,4) are actual raw ratios. -/
theorem exactA1B4 : ∀ c d : ZMod 8,
    IsExactWitness 1 4 c d 0
      (packedByteAt targetBytesA1B4 (pairLeafIndex c d)) := by
  decide +kernel

end RealPChiCertificate
end Superfusion.RMod.RawDCT
