import Superfusion.RMod.RawDCT.RealPChiCertificateCore

/-!
# Exact real pentagon certificate leaf: first labels (6,4)

The packed bytes are candidate target coordinates extracted by the existing
exact certgen BOT scan.  The theorem independently rechecks the actual
realTData.hom TOP/BOT coefficients with decide +kernel.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT
namespace RealPChiCertificate

/-! ## Packed coordinate data -/

/-- First nonzero flat BOT target coordinate for each (6,4,c,d). -/
def targetBytesA6B4 : ℕ := 0x400030600010203000000120103010100000003000100030202021201040602090001080000000c0600030809180c0a0003010618040001030103020c0a0100

/-! ## Kernel-checked law -/

/-- All 64 entries with first labels (6,4) are actual raw ratios. -/
theorem exactA6B4 : ∀ c d : ZMod 8,
    IsExactWitness 6 4 c d 0
      (packedByteAt targetBytesA6B4 (pairLeafIndex c d)) := by
  decide +kernel

end RealPChiCertificate
end Superfusion.RMod.RawDCT
