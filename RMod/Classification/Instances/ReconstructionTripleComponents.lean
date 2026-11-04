import RMod.Classification.Instances.ReconstructionTensorComponents
import RMod.Classification.Instances.ReconstructionTensorBicone
import RMod.Classification.Instances.OrbitTensorSpan

/-!
# Source component maps for the two triple tensor presentations

Keep the two parenthesizations in their intrinsic product degrees. The
inclusions are the actual threefold tensor inclusions followed by the
selected output projection. They retain the maps needed to compare the
global tensorator composites with the component associativity diagram.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

variable (A : PiSuperfusion.{0, 0})
  (X Y Z : LinearCategory A.toWeaklyPointedSuperfusion)
  (g h k : SimpleOrbit A.toWeaklyPointedSuperfusion)

noncomputable def reconstructionTensorSpanInclusion :
    reconstructionTensorSpanObject A X Y g h ⟶
      (reconstructionSourceEquivalence A).inverse.obj (A.data.tensorObj X Y) (g * h) :=
  ObjectProperty.homMk (A.data.comp ((reconstructionTensorBicone A X Y).ι (g, h))
    ((reconstructionSourceBicone A (A.data.tensorObj X Y)).π (g * h)))

noncomputable def reconstructionTripleLeftSpan :=
  orbitTensorSpanObj A.toWeaklyPointedSuperfusion (g * h) k
    (reconstructionTensorSpanObject A X Y g h)
    ((reconstructionSourceEquivalence A).inverse.obj Z k)

noncomputable def reconstructionTripleRightSpan :=
  orbitTensorSpanObj A.toWeaklyPointedSuperfusion g (h * k)
    ((reconstructionSourceEquivalence A).inverse.obj X g)
    (reconstructionTensorSpanObject A Y Z h k)

noncomputable def reconstructionTripleLeftInclusion :
    reconstructionTripleLeftSpan A X Y Z g h k ⟶
      (reconstructionSourceEquivalence A).inverse.obj
        (A.data.tensorObj (A.data.tensorObj X Y) Z) ((g * h) * k) :=
  ObjectProperty.homMk (A.data.comp
    (A.data.tensorHom ((reconstructionTensorBicone A X Y).ι (g, h)) ((reconstructionSourceBicone A Z).ι k))
    ((reconstructionSourceBicone A (A.data.tensorObj (A.data.tensorObj X Y) Z)).π ((g * h) * k)))

noncomputable def reconstructionTripleRightInclusion :
    reconstructionTripleRightSpan A X Y Z g h k ⟶
      (reconstructionSourceEquivalence A).inverse.obj
        (A.data.tensorObj X (A.data.tensorObj Y Z)) (g * (h * k)) :=
  ObjectProperty.homMk (A.data.comp
    (A.data.tensorHom ((reconstructionSourceBicone A X).ι g) ((reconstructionTensorBicone A Y Z).ι (h, k)))
    ((reconstructionSourceBicone A (A.data.tensorObj X (A.data.tensorObj Y Z))).π (g * (h * k))))

end RMod.Classification
