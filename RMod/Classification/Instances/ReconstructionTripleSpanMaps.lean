import RMod.Classification.Instances.ReconstructionTripleComponents

/-!
# The source associator in a fixed output component

Group associativity lets either triple tensor object be presented in
both product spans. The associator keeps its ambient map, and the right
triple inclusion can use the left-associated output projection. These
presentations permit application of a single component functor.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

variable (A : PiSuperfusion.{0, 0}) (X Y Z : LinearCategory A.toWeaklyPointedSuperfusion)
  (g h k : SimpleOrbit A.toWeaklyPointedSuperfusion)

noncomputable def reconstructionTripleRightSpanAtLeft :
    HomogeneousSpanCategory A.toWeaklyPointedSuperfusion
      (simpleOrbitRepresentative A.toWeaklyPointedSuperfusion ((g * h) * k)).data.object := by
  let T : A.data.Obj := (reconstructionTripleRightSpan A X Y Z g h k).obj
  have hm : InHomogeneousSpan A.toWeaklyPointedSuperfusion
      (simpleOrbitRepresentative A.toWeaklyPointedSuperfusion (g * (h * k))).data.object T :=
    (reconstructionTripleRightSpan A X Y Z g h k).property
  rw [← mul_assoc] at hm
  exact ⟨T, hm⟩

noncomputable def reconstructionTripleLeftSpanAtRight :
    HomogeneousSpanCategory A.toWeaklyPointedSuperfusion
      (simpleOrbitRepresentative A.toWeaklyPointedSuperfusion (g * (h * k))).data.object := by
  let T : A.data.Obj := (reconstructionTripleLeftSpan A X Y Z g h k).obj
  have hm : InHomogeneousSpan A.toWeaklyPointedSuperfusion
      (simpleOrbitRepresentative A.toWeaklyPointedSuperfusion ((g * h) * k)).data.object T :=
    (reconstructionTripleLeftSpan A X Y Z g h k).property
  rw [mul_assoc] at hm
  exact ⟨T, hm⟩

noncomputable def reconstructionTripleAssociatorAtLeft :
    reconstructionTripleLeftSpan A X Y Z g h k ⟶ reconstructionTripleRightSpanAtLeft A X Y Z g h k :=
  ObjectProperty.homMk (A.data.associatorHom
    ((reconstructionSourceEquivalence A).inverse.obj X g).obj
    ((reconstructionSourceEquivalence A).inverse.obj Y h).obj
    ((reconstructionSourceEquivalence A).inverse.obj Z k).obj)

noncomputable def reconstructionTripleAssociatorAtRight :
    reconstructionTripleLeftSpanAtRight A X Y Z g h k ⟶ reconstructionTripleRightSpan A X Y Z g h k :=
  ObjectProperty.homMk (A.data.associatorHom
    ((reconstructionSourceEquivalence A).inverse.obj X g).obj
    ((reconstructionSourceEquivalence A).inverse.obj Y h).obj
    ((reconstructionSourceEquivalence A).inverse.obj Z k).obj)

noncomputable def reconstructionTripleRightInclusionAtLeft :
    reconstructionTripleRightSpanAtLeft A X Y Z g h k ⟶
      (reconstructionSourceEquivalence A).inverse.obj
        (A.data.tensorObj X (A.data.tensorObj Y Z)) ((g * h) * k) :=
  ObjectProperty.homMk (A.data.comp
    (A.data.tensorHom ((reconstructionSourceBicone A X).ι g) ((reconstructionTensorBicone A Y Z).ι (h, k)))
    ((reconstructionSourceBicone A (A.data.tensorObj X (A.data.tensorObj Y Z))).π ((g * h) * k)))

end RMod.Classification
