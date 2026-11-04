import Superfusion.RMod.RawDCT.RealPChiCertificateCore

/-!
# Exact real pentagon certificate leaf: first labels (5,2,3)

These candidate target bytes are the corresponding eight-byte slice of the
existing exact certgen BOT scan. The law independently checks all eight
actual TOP/BOT ratios with `decide +kernel`.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT
namespace RealPChiCertificate

/-- First nonzero flat BOT target coordinate for (5,2,3,d). -/
def targetBytesA5B2C3 : ℕ := 0x100010000000000

/-- All eight entries with first labels (5,2,3) are actual. -/
theorem exactA5B2C3 : ∀ d : ZMod 8,
    IsExactWitness 5 2 3 d 0
      (packedByteAt targetBytesA5B2C3 d.val) := by
  decide +kernel

end RealPChiCertificate
end Superfusion.RMod.RawDCT

