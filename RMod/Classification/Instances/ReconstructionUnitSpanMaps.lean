import RMod.Classification.Instances.ReconstructionTensorComponents
import RMod.Classification.Instances.ReconstructionSourceBicone

/-!
# Unit tensor objects and maps in their fixed output components

The group unit laws place the tensors of the selected unit component
and the g component back in the g span. The retained inclusion of the
unit component followed by the ambient unitor gives the actual maps.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

variable (A : PiSuperfusion.{0, 0}) (X : LinearCategory A.toWeaklyPointedSuperfusion)
  (g : SimpleOrbit A.toWeaklyPointedSuperfusion)

noncomputable def reconstructionLeftUnitSpan :
    HomogeneousSpanCategory A.toWeaklyPointedSuperfusion
      (simpleOrbitRepresentative A.toWeaklyPointedSuperfusion g).data.object := by
  refine ⟨A.data.tensorObj ((reconstructionSourceEquivalence A).inverse.obj A.data.tensorUnit 1).obj
    ((reconstructionSourceEquivalence A).inverse.obj X g).obj, ?_⟩
  have hm : InHomogeneousSpan A.toWeaklyPointedSuperfusion
      (simpleOrbitRepresentative A.toWeaklyPointedSuperfusion (1 * g)).data.object
      (A.data.tensorObj ((reconstructionSourceEquivalence A).inverse.obj A.data.tensorUnit 1).obj
        ((reconstructionSourceEquivalence A).inverse.obj X g).obj) :=
    (reconstructionTensorSpanObject A A.data.tensorUnit X 1 g).property
  rw [one_mul] at hm
  exact hm

noncomputable def reconstructionRightUnitSpan :
    HomogeneousSpanCategory A.toWeaklyPointedSuperfusion
      (simpleOrbitRepresentative A.toWeaklyPointedSuperfusion g).data.object := by
  refine ⟨A.data.tensorObj ((reconstructionSourceEquivalence A).inverse.obj X g).obj
    ((reconstructionSourceEquivalence A).inverse.obj A.data.tensorUnit 1).obj, ?_⟩
  have hm : InHomogeneousSpan A.toWeaklyPointedSuperfusion
      (simpleOrbitRepresentative A.toWeaklyPointedSuperfusion (g * 1)).data.object
      (A.data.tensorObj ((reconstructionSourceEquivalence A).inverse.obj X g).obj
        ((reconstructionSourceEquivalence A).inverse.obj A.data.tensorUnit 1).obj) :=
    (reconstructionTensorSpanObject A X A.data.tensorUnit g 1).property
  rw [mul_one] at hm
  exact hm

noncomputable def reconstructionLeftUnitSpanMap :
    reconstructionLeftUnitSpan A X g ⟶ (reconstructionSourceEquivalence A).inverse.obj X g :=
  ObjectProperty.homMk (A.data.comp
    (A.data.tensorHom ((reconstructionSourceBicone A A.data.tensorUnit).ι 1)
      (A.data.id ((reconstructionSourceEquivalence A).inverse.obj X g).obj))
    (A.data.leftUnitorHom ((reconstructionSourceEquivalence A).inverse.obj X g).obj))

noncomputable def reconstructionRightUnitSpanMap :
    reconstructionRightUnitSpan A X g ⟶ (reconstructionSourceEquivalence A).inverse.obj X g :=
  ObjectProperty.homMk (A.data.comp
    (A.data.tensorHom (A.data.id ((reconstructionSourceEquivalence A).inverse.obj X g).obj)
      ((reconstructionSourceBicone A A.data.tensorUnit).ι 1))
    (A.data.rightUnitorHom ((reconstructionSourceEquivalence A).inverse.obj X g).obj))

end RMod.Classification
