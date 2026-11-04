import RMod.Classification.Instances.ReconstructionTensorComponents

/-! # Actual tensor maps between the selected source components -/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

variable (A : PiSuperfusion.{0, 0}) {X X' Y Y' : LinearCategory A.toWeaklyPointedSuperfusion}

noncomputable def reconstructionTensorSpanMap (f : X ⟶ X') (h : Y ⟶ Y')
    (g k : SimpleOrbit A.toWeaklyPointedSuperfusion) :
    reconstructionTensorSpanObject A X Y g k ⟶ reconstructionTensorSpanObject A X' Y' g k :=
  ObjectProperty.homMk (A.data.tensorHom ((reconstructionSourceEquivalence A).inverse.map f g).hom
    ((reconstructionSourceEquivalence A).inverse.map h k).hom)

noncomputable def reconstructionTensorOutputSpanMap (f : X ⟶ X') (h : Y ⟶ Y')
    (k g : SimpleOrbit A.toWeaklyPointedSuperfusion) :
    reconstructionTensorOutputSpan A X Y k g ⟶ reconstructionTensorOutputSpan A X' Y' k g :=
  ObjectProperty.homMk (A.data.tensorHom ((reconstructionSourceEquivalence A).inverse.map f g).hom
    ((reconstructionSourceEquivalence A).inverse.map h (g⁻¹ * k)).hom)

end RMod.Classification
