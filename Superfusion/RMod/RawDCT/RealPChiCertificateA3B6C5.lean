import Superfusion.RMod.RawDCT.RealPChiCertificateCore

/-!
# Exact real pentagon certificate leaf: first labels (3,6,5)

These candidate target bytes come from the existing exact certgen BOT scan.
The law independently checks all eight actual TOP/BOT ratios with
`decide +kernel`.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT
namespace RealPChiCertificate

/-- First nonzero flat BOT target coordinate for (3,6,5,d). -/
def targetBytesA3B6C5 : ℕ := 0x100000001000000

/-- All eight entries with first labels (3,6,5) are actual. -/
theorem exactA3B6C5 : ∀ d : ZMod 8,
    IsExactWitness 3 6 5 d 0
      (packedByteAt targetBytesA3B6C5 d.val) := by
  decide +kernel

end RealPChiCertificate
end Superfusion.RMod.RawDCT
