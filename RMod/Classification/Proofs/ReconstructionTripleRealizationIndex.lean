import RMod.Classification.Instances.ReconstructionTripleSpanMaps
import RMod.Classification.Instances.ReconstructionMappedTensorBicone
import Batteries.Tactic.GeneralizeProofs

/-!
# Equality of the actual triple component images under group associativity

The full-subcategory presentations have the same underlying tensor
objects. Their component images agree when the two product indices are
identified; the proof keeps these object equality maps explicit.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (A C : PiSuperfusion.{0, 0}) (hC : ReferenceProperty C.data)
  (X Y Z : LinearCategory A.toWeaklyPointedSuperfusion)
  (g h k : SimpleOrbit A.toWeaklyPointedSuperfusion)

theorem reconstructionTripleLeftRealization_index :
    (reconstructionComponentRealization A C hC ((g * h) * k)).obj
      (reconstructionTripleLeftSpan A X Y Z g h k) =
    (reconstructionComponentRealization A C hC (g * (h * k))).obj
      (reconstructionTripleLeftSpanAtRight A X Y Z g h k) := by
  let T : LinearCategory A.toWeaklyPointedSuperfusion := (reconstructionTripleLeftSpan A X Y Z g h k).obj
  change (reconstructionComponentRealization A C hC ((g * h) * k)).obj ⟨T, _⟩ =
    (reconstructionComponentRealization A C hC (g * (h * k))).obj ⟨T, _⟩
  generalize_proofs hL hR
  revert hL hR
  rw [mul_assoc]
  intro hL hR
  rfl

theorem reconstructionTripleRightRealization_index :
    (reconstructionComponentRealization A C hC ((g * h) * k)).obj
      (reconstructionTripleRightSpanAtLeft A X Y Z g h k) =
    (reconstructionComponentRealization A C hC (g * (h * k))).obj
      (reconstructionTripleRightSpan A X Y Z g h k) := by
  let T : LinearCategory A.toWeaklyPointedSuperfusion := (reconstructionTripleRightSpan A X Y Z g h k).obj
  change (reconstructionComponentRealization A C hC ((g * h) * k)).obj ⟨T, _⟩ =
    (reconstructionComponentRealization A C hC (g * (h * k))).obj ⟨T, _⟩
  generalize_proofs hL hR
  revert hL hR
  rw [mul_assoc]
  intro hL hR
  rfl

end RMod.Classification
