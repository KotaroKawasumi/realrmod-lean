import RMod.Classification.Instances.ReconstructionTensorBlock
import RMod.Classification.Instances.ReconstructionUnitSpanMaps
import Batteries.Tactic.GeneralizeProofs

/-!
# Product and fixed-degree presentations of the selected unit tensor

The group unit equations identify the image of the actual selected unit
component tensor with its image in the fixed output span. These are the
equality maps that occur in the global convolution tensorator.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (A C : PiSuperfusion.{0, 0}) (hC : ReferenceProperty C.data)
  (X : LinearCategory A.toWeaklyPointedSuperfusion)
  (g : SimpleOrbit A.toWeaklyPointedSuperfusion)

theorem reconstructionLeftUnitComponent_obj :
    (reconstructionComponentRealization A C hC (1 * g)).obj
      (reconstructionTensorSpanObject A A.data.tensorUnit X 1 g) =
    (reconstructionComponentRealization A C hC g).obj (reconstructionLeftUnitSpan A X g) := by
  change (reconstructionComponentRealization A C hC (1 * g)).obj ⟨_, _⟩ = _
  generalize_proofs hmem
  revert hmem
  rw [one_mul]
  intro hmem
  rfl

theorem reconstructionRightUnitComponent_obj :
    (reconstructionComponentRealization A C hC (g * 1)).obj
      (reconstructionTensorSpanObject A X A.data.tensorUnit g 1) =
    (reconstructionComponentRealization A C hC g).obj (reconstructionRightUnitSpan A X g) := by
  change (reconstructionComponentRealization A C hC (g * 1)).obj ⟨_, _⟩ = _
  generalize_proofs hmem
  revert hmem
  rw [mul_one]
  intro hmem
  rfl

end RMod.Classification
