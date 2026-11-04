import Superfusion.RMod.RawDCT.RealPChiCertificateCore

/-!
# Exact real pentagon certificate leaf: first labels (3,3,2)

These candidate target bytes are the corresponding eight-byte slice of the
existing exact certgen BOT scan. The law independently checks all eight
actual TOP/BOT ratios with `decide +kernel`.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT
namespace RealPChiCertificate

/-- First nonzero flat BOT target coordinate for (3,3,2,d). -/
def targetBytesA3B3C2 : ℕ := 0x103010404000007

/-- All eight entries with first labels (3,3,2) are actual. -/
theorem exactA3B3C2 : ∀ d : ZMod 8,
    IsExactWitness 3 3 2 d 0
      (packedByteAt targetBytesA3B3C2 d.val) := by
  decide +kernel

end RealPChiCertificate
end Superfusion.RMod.RawDCT

