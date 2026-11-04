import RMod.Classification.Instances.ReconstructionTripleSpanMaps
import RMod.Classification.Proofs.ReconstructionTripleAssociator

/-!
# The source triple associativity square in one full component category

The equality of product indices transports the actual right inclusion
to the left output degree. The retained associator equation therefore
becomes an equation of morphisms in that single homogeneous span.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

variable (A : PiSuperfusion.{0, 0}) (X Y Z : LinearCategory A.toWeaklyPointedSuperfusion)
  (g h k : SimpleOrbit A.toWeaklyPointedSuperfusion)

theorem reconstructionTripleRightInclusion_index :
    A.data.comp (reconstructionTripleRightInclusion A X Y Z g h k).hom
      (IsoData.ofEq A.toWeaklyPointedSuperfusion.data
        (congrArg (fun j => ((reconstructionSourceEquivalence A).inverse.obj
          (A.data.tensorObj X (A.data.tensorObj Y Z)) j).obj) (mul_assoc g h k))).inv =
      (reconstructionTripleRightInclusionAtLeft A X Y Z g h k).hom := by
  let T : A.data.Obj := A.data.tensorObj X (A.data.tensorObj Y Z)
  let P : SimpleOrbit A.toWeaklyPointedSuperfusion → A.data.Obj :=
    fun j => ((reconstructionSourceEquivalence A).inverse.obj T j).obj
  let i : A.data.Hom (reconstructionTripleRightSpan A X Y Z g h k).obj T :=
    A.data.tensorHom ((reconstructionSourceBicone A X).ι g) ((reconstructionTensorBicone A Y Z).ι (h, k))
  let p : ∀ j, A.data.Hom T (P j) := (reconstructionSourceBicone A T).π
  have hp := indexed_map_to_eq A.toWeaklyPointedSuperfusion P p (mul_assoc g h k)
  exact (A.laws.comp_assoc _ _ _).trans (congrArg (A.data.comp i) hp)

theorem reconstructionTripleInclusion_associator_at_left :
    reconstructionTripleLeftInclusion A X Y Z g h k ≫
      (reconstructionSourceEquivalence A).inverse.map (A.data.associatorHom X Y Z) ((g * h) * k) =
    reconstructionTripleAssociatorAtLeft A X Y Z g h k ≫
      reconstructionTripleRightInclusionAtLeft A X Y Z g h k := by
  apply ObjectProperty.hom_ext
  exact (reconstructionTripleInclusion_associator A X Y Z g h k).trans
    ((A.laws.comp_assoc _ _ _).trans
      (congrArg (A.data.comp (reconstructionTripleAssociatorAtLeft A X Y Z g h k).hom)
        (reconstructionTripleRightInclusion_index A X Y Z g h k)))

end RMod.Classification
