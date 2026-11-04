import Superfusion.RMod.RawDCT.RealPChiCertificateCore

/-!
# Exact real pentagon certificate leaf: first labels (3,5,5)

These candidate target bytes come from the existing exact certgen BOT scan.
The law independently checks all eight actual TOP/BOT ratios with
decide +kernel.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT
namespace RealPChiCertificate

/-- First nonzero flat BOT target coordinate for (3,5,5,d). -/
def targetBytesA3B5C5 : ℕ := 0x507000100000008

/-- All eight entries with first labels (3,5,5) are actual. -/
theorem exactA3B5C5 : ∀ d : ZMod 8,
    IsExactWitness 3 5 5 d 0
      (packedByteAt targetBytesA3B5C5 d.val) := by
  decide +kernel

end RealPChiCertificate
end Superfusion.RMod.RawDCT
