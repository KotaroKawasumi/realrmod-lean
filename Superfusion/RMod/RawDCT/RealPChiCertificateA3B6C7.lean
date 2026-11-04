import Superfusion.RMod.RawDCT.RealPChiCertificateCore

/-!
# Exact real pentagon certificate leaf: first labels (3,6,7)

These candidate target bytes come from the existing exact certgen BOT scan.
The law independently checks all eight actual TOP/BOT ratios with
`decide +kernel`.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT
namespace RealPChiCertificate

/-- First nonzero flat BOT target coordinate for (3,6,7,d). -/
def targetBytesA3B6C7 : ℕ := 0x50001000100

/-- All eight entries with first labels (3,6,7) are actual. -/
theorem exactA3B6C7 : ∀ d : ZMod 8,
    IsExactWitness 3 6 7 d 0
      (packedByteAt targetBytesA3B6C7 d.val) := by
  decide +kernel

end RealPChiCertificate
end Superfusion.RMod.RawDCT
