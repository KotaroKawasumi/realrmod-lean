import Superfusion.RMod.RawDCT.RealPChiCertificateCore

/-!
# Exact real pentagon certificate leaf: first labels (3,3,0)

These candidate target bytes are the corresponding eight-byte slice of the
existing exact certgen BOT scan. The law independently checks all eight
actual TOP/BOT ratios with `decide +kernel`.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT
namespace RealPChiCertificate

/-- First nonzero flat BOT target coordinate for (3,3,0,d). -/
def targetBytesA3B3C0 : ℕ := 0x414000300070400

/-- All eight entries with first labels (3,3,0) are actual. -/
theorem exactA3B3C0 : ∀ d : ZMod 8,
    IsExactWitness 3 3 0 d 0
      (packedByteAt targetBytesA3B3C0 d.val) := by
  decide +kernel

end RealPChiCertificate
end Superfusion.RMod.RawDCT

