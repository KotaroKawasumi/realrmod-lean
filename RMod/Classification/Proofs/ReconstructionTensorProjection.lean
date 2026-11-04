import RMod.Classification.Instances.ReconstructionTensorBicone
import RMod.Classification.Instances.ReconstructionTensorComponents
import RMod.Classification.Proofs.ReconstructionComponentProjection

/-!
# Selecting exactly the tensor factors of a given product degree

The degree-k projector fixes the pair (g,g^-1*k). Entries from its
component into any pair with product different from k vanish by simple
orbit orthogonality. These are the two hypotheses for graph selection.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory CategoryTheory.Limits

variable (A : PiSuperfusion.{0, 0}) (X Y : LinearCategory A.toWeaklyPointedSuperfusion)

theorem reconstructionTensorProjection_graph (k g : SimpleOrbit A.toWeaklyPointedSuperfusion) :
    (reconstructionTensorBicone A X Y).ι (g, g⁻¹ * k) ≫
      (reconstructionSourceBicone A (A.data.tensorObj X Y)).π k ≫
      (reconstructionSourceBicone A (A.data.tensorObj X Y)).ι k =
        (reconstructionTensorBicone A X Y).ι (g, g⁻¹ * k) := by
  apply reconstructionComponentProjection_incoming A k
  exact (reconstructionTensorOutputSpan A X Y k g).property

theorem reconstructionTensorProjection_zero (k g h : SimpleOrbit A.toWeaklyPointedSuperfusion)
    (hh : h ≠ g⁻¹ * k) :
    (reconstructionSourceBicone A (A.data.tensorObj X Y)).ι k ≫
      (reconstructionTensorBicone A X Y).π (g, h) = 0 := by
  have hk : k ≠ g * h := fun he => hh (by rw [he, inv_mul_cancel_left])
  exact hom_zero_of_distinct_spans A.toWeaklyPointedSuperfusion
    (simpleOrbitRepresentative A.toWeaklyPointedSuperfusion k).laws.simple
    (simpleOrbitRepresentative A.toWeaklyPointedSuperfusion (g * h)).laws.simple
    (simpleOrbitRepresentatives_separate A.toWeaklyPointedSuperfusion k (g * h) hk)
    ((reconstructionSourceEquivalence A).inverse.obj (A.data.tensorObj X Y) k).property
    (reconstructionTensorSpanObject A X Y g h).property _

end RMod.Classification
