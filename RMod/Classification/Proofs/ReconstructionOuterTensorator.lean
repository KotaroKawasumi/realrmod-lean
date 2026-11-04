import RMod.Classification.Instances.ReconstructionMappedTripleComponents
import RMod.Classification.Instances.ReconstructionOmega
import RMod.Classification.Proofs.ReconstructionTriplePresentation
import RMod.Classification.Proofs.ParityTensorComparisonNaturality

/-!
# Moving an inner component inclusion through the outer tensorator

Full-Hom naturality of the binary comparison moves the selected inner
inclusion through the outer tensorator. Functoriality then combines the
two mapped inclusions into the retained triple inclusion.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

variable (A C : PiSuperfusion.{0, 0}) (hC : ReferenceProperty C.data)
  (X Y Z : LinearCategory A.toWeaklyPointedSuperfusion)
  (g h k : SimpleOrbit A.toWeaklyPointedSuperfusion)

theorem reconstructionOuterTensorator_left_inclusion :
    C.data.comp (C.data.comp
      (C.data.tensorHom (C.data.tensorHom (reconstructionMappedTensorSpanInclusion A C hC X Y g h) (C.data.id (((reconstructionUnderlyingEquivalence A C hC).functor.obj Z) k).val)) (C.data.id (C.data.pi.factor (reconstructionNu A C hC (g * h) k))))
      ((reconstructionTensorComparison A C hC (g * h) k).data.app ((reconstructionSourceEquivalence A).inverse.obj (A.data.tensorObj X Y) (g * h)) ((reconstructionSourceEquivalence A).inverse.obj Z k)).hom)
      (reconstructionMappedTensorSpanInclusion A C hC (A.data.tensorObj X Y) Z (g * h) k) =
    C.data.comp ((reconstructionTensorComparison A C hC (g * h) k).data.app (reconstructionTensorSpanObject A X Y g h) ((reconstructionSourceEquivalence A).inverse.obj Z k)).hom
      (reconstructionMappedTripleLeftInclusion A C hC X Y Z g h k) := by
  let η := reconstructionTensorComparison A C hC (g * h) k
  let F := reconstructionComponentRealization A C hC ((g * h) * k)
  let f := orbitTensorSpanHom A.toWeaklyPointedSuperfusion (g * h) k (reconstructionTensorSpanInclusion A X Y g h) (𝟙 ((reconstructionSourceEquivalence A).inverse.obj Z k))
  let q := reconstructionTensorSpanInclusion A (A.data.tensorObj X Y) Z (g * h) k
  have hs : f ≫ q = reconstructionTripleLeftInclusion A X Y Z g h k := by
    apply ObjectProperty.hom_ext
    exact reconstructionTripleLeftInclusion_nested A X Y Z g h k
  have hm := (F.map_comp f q).symm.trans (congrArg F.map hs)
  have hn := η.naturality_all (reconstructionTensorSpanInclusion A X Y g h) (𝟙 ((reconstructionSourceEquivalence A).inverse.obj Z k))
  have hid : (((reconstructionComponentSystem A C hC).component k).forwardFunctor.data.map (𝟙 ((reconstructionSourceEquivalence A).inverse.obj Z k))).hom =
      C.data.id (((reconstructionUnderlyingEquivalence A C hC).functor.obj Z) k).val :=
    congrArg (fun m => m.hom) (((reconstructionComponentSystem A C hC).component k).forwardFunctor.laws.map_id ((reconstructionSourceEquivalence A).inverse.obj Z k))
  rw [hid] at hn
  exact (congrArg (fun m => C.data.comp m (F.map q)) hn).trans
    ((C.laws.comp_assoc _ _ _).trans
      (congrArg (C.data.comp (η.data.app (reconstructionTensorSpanObject A X Y g h) ((reconstructionSourceEquivalence A).inverse.obj Z k)).hom) hm))

theorem reconstructionOuterTensorator_right_inclusion :
    C.data.comp (C.data.comp
      (C.data.tensorHom (C.data.tensorHom (C.data.id (((reconstructionUnderlyingEquivalence A C hC).functor.obj X) g).val) (reconstructionMappedTensorSpanInclusion A C hC Y Z h k)) (C.data.id (C.data.pi.factor (reconstructionNu A C hC g (h * k)))))
      ((reconstructionTensorComparison A C hC g (h * k)).data.app ((reconstructionSourceEquivalence A).inverse.obj X g) ((reconstructionSourceEquivalence A).inverse.obj (A.data.tensorObj Y Z) (h * k))).hom)
      (reconstructionMappedTensorSpanInclusion A C hC X (A.data.tensorObj Y Z) g (h * k)) =
    C.data.comp ((reconstructionTensorComparison A C hC g (h * k)).data.app ((reconstructionSourceEquivalence A).inverse.obj X g) (reconstructionTensorSpanObject A Y Z h k)).hom
      (reconstructionMappedTripleRightInclusion A C hC X Y Z g h k) := by
  let η := reconstructionTensorComparison A C hC g (h * k)
  let F := reconstructionComponentRealization A C hC (g * (h * k))
  let f := orbitTensorSpanHom A.toWeaklyPointedSuperfusion g (h * k) (𝟙 ((reconstructionSourceEquivalence A).inverse.obj X g)) (reconstructionTensorSpanInclusion A Y Z h k)
  let q := reconstructionTensorSpanInclusion A X (A.data.tensorObj Y Z) g (h * k)
  have hs : f ≫ q = reconstructionTripleRightInclusion A X Y Z g h k := by
    apply ObjectProperty.hom_ext
    exact reconstructionTripleRightInclusion_nested A X Y Z g h k
  have hm := (F.map_comp f q).symm.trans (congrArg F.map hs)
  have hn := η.naturality_all (𝟙 ((reconstructionSourceEquivalence A).inverse.obj X g)) (reconstructionTensorSpanInclusion A Y Z h k)
  have hid : (((reconstructionComponentSystem A C hC).component g).forwardFunctor.data.map (𝟙 ((reconstructionSourceEquivalence A).inverse.obj X g))).hom =
      C.data.id (((reconstructionUnderlyingEquivalence A C hC).functor.obj X) g).val :=
    congrArg (fun m => m.hom) (((reconstructionComponentSystem A C hC).component g).forwardFunctor.laws.map_id ((reconstructionSourceEquivalence A).inverse.obj X g))
  rw [hid] at hn
  exact (congrArg (fun m => C.data.comp m (F.map q)) hn).trans
    ((C.laws.comp_assoc _ _ _).trans
      (congrArg (C.data.comp (η.data.app ((reconstructionSourceEquivalence A).inverse.obj X g) (reconstructionTensorSpanObject A Y Z h k)).hom) hm))

end RMod.Classification
