import Superfusion.RMod.RawDCT.RealPChiCertificateCore

/-!
# Exact real pentagon certificate leaf: first labels (2,5,0)

These candidate target bytes come from the existing exact certgen BOT scan.
The law independently checks all eight actual TOP/BOT ratios with
decide +kernel.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT
namespace RealPChiCertificate

/-- First nonzero flat BOT target coordinate for (2,5,0,d). -/
def targetBytesA2B5C0 : ℕ := 0x104040200030000

/-- All eight entries with first labels (2,5,0) are actual. -/
theorem exactA2B5C0 : ∀ d : ZMod 8,
    IsExactWitness 2 5 0 d 0
      (packedByteAt targetBytesA2B5C0 d.val) := by
  decide +kernel

end RealPChiCertificate
end Superfusion.RMod.RawDCT
