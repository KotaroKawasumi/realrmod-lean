import Superfusion.RMod.RawDCT.RealPChiCertificateCore

/-!
# Exact real pentagon certificate leaf: first labels (5,5,7)

These candidate target bytes are the corresponding eight-byte slice of the
existing exact certgen BOT scan. The law independently checks all eight
actual TOP/BOT ratios with `decide +kernel`.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT
namespace RealPChiCertificate

/-- First nonzero flat BOT target coordinate for (5,5,7,d). -/
def targetBytesA5B5C7 : ℕ := 0x100050121020200

/-- All eight entries with first labels (5,5,7) are actual. -/
theorem exactA5B5C7 : ∀ d : ZMod 8,
    IsExactWitness 5 5 7 d 0
      (packedByteAt targetBytesA5B5C7 d.val) := by
  decide +kernel

end RealPChiCertificate
end Superfusion.RMod.RawDCT

