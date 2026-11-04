import Superfusion.RMod.RawDCT.RealPChiCertificateCore

/-!
# Exact real pentagon certificate leaf: first labels (2,5,1)

These candidate target bytes come from the existing exact certgen BOT scan.
The law independently checks all eight actual TOP/BOT ratios with
decide +kernel.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT
namespace RealPChiCertificate

/-- First nonzero flat BOT target coordinate for (2,5,1,d). -/
def targetBytesA2B5C1 : ℕ := 0x101030001030100

/-- All eight entries with first labels (2,5,1) are actual. -/
theorem exactA2B5C1 : ∀ d : ZMod 8,
    IsExactWitness 2 5 1 d 0
      (packedByteAt targetBytesA2B5C1 d.val) := by
  decide +kernel

end RealPChiCertificate
end Superfusion.RMod.RawDCT
