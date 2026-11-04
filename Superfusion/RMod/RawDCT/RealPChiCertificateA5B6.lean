import Superfusion.RMod.RawDCT.RealPChiCertificateCore

/-!
# Exact real pentagon certificate leaf: first labels (5,6)

The packed bytes are candidate target coordinates extracted by the existing
exact certgen BOT scan.  The theorem independently rechecks the actual
realTData.hom TOP/BOT coefficients with decide +kernel.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT
namespace RealPChiCertificate

/-! ## Packed coordinate data -/

/-- First nonzero flat BOT target coordinate for each (5,6,c,d). -/
def targetBytesA5B6 : ℕ := 0x40300050004000401010100060001000100010700000601002000080305000533000306010301120129080003090103010000010000090001060001010900

/-! ## Kernel-checked law -/

/-- All 64 entries with first labels (5,6) are actual raw ratios. -/
theorem exactA5B6 : ∀ c d : ZMod 8,
    IsExactWitness 5 6 c d 0
      (packedByteAt targetBytesA5B6 (pairLeafIndex c d)) := by
  decide +kernel

end RealPChiCertificate
end Superfusion.RMod.RawDCT
