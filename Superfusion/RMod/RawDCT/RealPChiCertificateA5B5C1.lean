import Superfusion.RMod.RawDCT.RealPChiCertificateCore

/-!
# Exact real pentagon certificate leaf: first labels (5,5,1)

These candidate target bytes are the corresponding eight-byte slice of the
existing exact certgen BOT scan. The law independently checks all eight
actual TOP/BOT ratios with `decide +kernel`.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT
namespace RealPChiCertificate

/-- First nonzero flat BOT target coordinate for (5,5,1,d). -/
def targetBytesA5B5C1 : ℕ := 0x40111061004

/-- All eight entries with first labels (5,5,1) are actual. -/
theorem exactA5B5C1 : ∀ d : ZMod 8,
    IsExactWitness 5 5 1 d 0
      (packedByteAt targetBytesA5B5C1 d.val) := by
  decide +kernel

end RealPChiCertificate
end Superfusion.RMod.RawDCT

