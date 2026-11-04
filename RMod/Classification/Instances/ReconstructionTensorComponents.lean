import RMod.Classification.Instances.ReconstructionSourceEquivalence
import RMod.Classification.Instances.SpanTensor
import RMod.Classification.Proofs.SimpleOrbitRepresentatives

/-!
# The actual tensor of two selected source components

Tensoring the g and h components gives an object of the g*h span.
Changing from the tensor generator to the chosen product representative
only changes the membership proof, retaining the ambient tensor object.
-/

set_option autoImplicit false

namespace RMod.Classification

noncomputable def reconstructionTensorSpanObject (A : PiSuperfusion.{0, 0})
    (X Y : LinearCategory A.toWeaklyPointedSuperfusion)
    (g h : SimpleOrbit A.toWeaklyPointedSuperfusion) :
    HomogeneousSpanCategory A.toWeaklyPointedSuperfusion
      (simpleOrbitRepresentative A.toWeaklyPointedSuperfusion (g * h)).data.object :=
  ⟨A.data.tensorObj ((reconstructionSourceEquivalence A).inverse.obj X g).obj
      ((reconstructionSourceEquivalence A).inverse.obj Y h).obj,
    (inHomogeneousSpan_congr_generator A.toWeaklyPointedSuperfusion
      (simpleTensorRepresentative A.toWeaklyPointedSuperfusion
        (simpleOrbitRepresentative A.toWeaklyPointedSuperfusion g)
        (simpleOrbitRepresentative A.toWeaklyPointedSuperfusion h)).laws.simple
      (simpleOrbitRepresentative A.toWeaklyPointedSuperfusion (g * h)).laws.simple
      (simpleOrbitRepresentative_mul A.toWeaklyPointedSuperfusion g h) _).mp
      (inHomogeneousSpan_tensor A.toWeaklyPointedSuperfusion _ _
        ((reconstructionSourceEquivalence A).inverse.obj X g).property
        ((reconstructionSourceEquivalence A).inverse.obj Y h).property)⟩

/-- The same tensor object, placed in the fixed output span k. -/
noncomputable def reconstructionTensorOutputSpan (A : PiSuperfusion.{0, 0})
    (X Y : LinearCategory A.toWeaklyPointedSuperfusion)
    (k g : SimpleOrbit A.toWeaklyPointedSuperfusion) :
    HomogeneousSpanCategory A.toWeaklyPointedSuperfusion
      (simpleOrbitRepresentative A.toWeaklyPointedSuperfusion k).data.object := by
  refine ⟨A.data.tensorObj ((reconstructionSourceEquivalence A).inverse.obj X g).obj
    ((reconstructionSourceEquivalence A).inverse.obj Y (g⁻¹ * k)).obj, ?_⟩
  have hm : InHomogeneousSpan A.toWeaklyPointedSuperfusion
      (simpleOrbitRepresentative A.toWeaklyPointedSuperfusion (g * (g⁻¹ * k))).data.object
      (A.data.tensorObj ((reconstructionSourceEquivalence A).inverse.obj X g).obj
        ((reconstructionSourceEquivalence A).inverse.obj Y (g⁻¹ * k)).obj) :=
    (reconstructionTensorSpanObject A X Y g (g⁻¹ * k)).property
  rw [mul_inv_cancel_left] at hm
  exact hm

end RMod.Classification
