import Superfusion.RMod.RawDCT.RealPChiCertificateA0
import Superfusion.RMod.RawDCT.RealPChiCertificateA1
import Superfusion.RMod.RawDCT.RealPChiCertificateA2
import Superfusion.RMod.RawDCT.RealPChiCertificateA3
import Superfusion.RMod.RawDCT.RealPChiCertificateA4
import Superfusion.RMod.RawDCT.RealPChiCertificateA5
import Superfusion.RMod.RawDCT.RealPChiCertificateA6
import Superfusion.RMod.RawDCT.RealPChiCertificateA7

/-!
# Complete exact certificate for the real raw pentagon table

The eight leaf files keep kernel reduction bounded.  This file joins their
packed coordinate data into one computable target-index function and joins
their already checked laws by finite case analysis.  It performs no further
fourfold coefficient calculation.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT
namespace RealPChiCertificate

/-! ## Complete computable witness data -/

/-- The selected flat target coordinate for every ordered quadruple.

The source coordinate is uniformly flat index zero.  The target coordinate
is read from the byte table belonging to the first label. -/
def targetIndex (a b c d : ZMod 8) : ℕ :=
  selectLabel a
    (targetIndexA0 b c d) (targetIndexA1 b c d)
    (targetIndexA2 b c d) (targetIndexA3 b c d)
    (targetIndexA4 b c d) (targetIndexA5 b c d)
    (targetIndexA6 b c d) (targetIndexA7 b c d)

/-! ## Complete kernel-checked law -/

/-- The deterministic source-zero/target-table pair checks the actual raw
fourfold ratio at every one of the 4096 ordered quadruples.  This theorem
only dispatches to the eight leaf laws; it does not repeat their reductions. -/
theorem exactWitness (a b c d : ZMod 8) :
    IsExactWitness a b c d 0 (targetIndex a b c d) := by
  rcases label_cases a with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · unfold targetIndex selectLabel
    rw [if_pos rfl]
    exact exactA0 b c d
  · unfold targetIndex selectLabel
    rw [if_neg (by decide), if_pos rfl]
    exact exactA1 b c d
  · unfold targetIndex selectLabel
    rw [if_neg (by decide), if_neg (by decide), if_pos rfl]
    exact exactA2 b c d
  · unfold targetIndex selectLabel
    rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl]
    exact exactA3 b c d
  · unfold targetIndex selectLabel
    rw [if_neg (by decide), if_neg (by decide), if_neg (by decide),
      if_neg (by decide), if_pos rfl]
    exact exactA4 b c d
  · unfold targetIndex selectLabel
    rw [if_neg (by decide), if_neg (by decide), if_neg (by decide),
      if_neg (by decide), if_neg (by decide), if_pos rfl]
    exact exactA5 b c d
  · unfold targetIndex selectLabel
    rw [if_neg (by decide), if_neg (by decide), if_neg (by decide),
      if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl]
    exact exactA6 b c d
  · unfold targetIndex selectLabel
    rw [if_neg (by decide), if_neg (by decide), if_neg (by decide),
      if_neg (by decide), if_neg (by decide), if_neg (by decide),
      if_neg (by decide)]
    exact exactA7 b c d

/-! ## Nontrivial closed witness evaluations -/

example : targetIndex 1 1 1 1 = 5 := by decide +kernel

example : targetIndex 5 5 5 5 = 64 := by decide +kernel

end RealPChiCertificate
end Superfusion.RMod.RawDCT
