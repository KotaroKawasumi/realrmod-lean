import Superfusion.RMod.RawDCT.RealPChiCertificateCore

/-!
# Exact real pentagon certificate leaf: first labels (3,3,6)

These candidate target bytes are the corresponding eight-byte slice of the
existing exact certgen BOT scan. The law independently checks all eight
actual TOP/BOT ratios with `decide +kernel`.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT
namespace RealPChiCertificate

/-- First nonzero flat BOT target coordinate for (3,3,6,d). -/
def targetBytesA3B3C6 : ℕ := 0x515010600010214

/-- All eight entries with first labels (3,3,6) are actual. -/
theorem exactA3B3C6 : ∀ d : ZMod 8,
    IsExactWitness 3 3 6 d 0
      (packedByteAt targetBytesA3B3C6 d.val) := by
  decide +kernel

end RealPChiCertificate
end Superfusion.RMod.RawDCT

