import Superfusion.RMod.RawDCT.RealPChiCertificateCore

/-!
# Exact real pentagon certificate leaf: first labels (3,7,1)

These candidate target bytes are the corresponding eight-byte slice of the
existing exact certgen BOT scan. The law independently checks all eight
actual TOP/BOT ratios with `decide +kernel`.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT
namespace RealPChiCertificate

/-- First nonzero flat BOT target coordinate for (3,7,1,d). -/
def targetBytesA3B7C1 : ℕ := 0x4000210040004

/-- All eight entries with first labels (3,7,1) are actual. -/
theorem exactA3B7C1 : ∀ d : ZMod 8,
    IsExactWitness 3 7 1 d 0
      (packedByteAt targetBytesA3B7C1 d.val) := by
  decide +kernel

end RealPChiCertificate
end Superfusion.RMod.RawDCT

