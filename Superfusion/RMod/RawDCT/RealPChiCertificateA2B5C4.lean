import Superfusion.RMod.RawDCT.RealPChiCertificateCore

/-!
# Exact real pentagon certificate leaf: first labels (2,5,4)

These candidate target bytes come from the existing exact certgen BOT scan.
The law independently checks all eight actual TOP/BOT ratios with
decide +kernel.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT
namespace RealPChiCertificate

/-- First nonzero flat BOT target coordinate for (2,5,4,d). -/
def targetBytesA2B5C4 : ℕ := 0x101080001110602

/-- All eight entries with first labels (2,5,4) are actual. -/
theorem exactA2B5C4 : ∀ d : ZMod 8,
    IsExactWitness 2 5 4 d 0
      (packedByteAt targetBytesA2B5C4 d.val) := by
  decide +kernel

end RealPChiCertificate
end Superfusion.RMod.RawDCT
