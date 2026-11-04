import RMod.Classification.Proofs.ReconstructionComponentAssociatorFormula
import RMod.Classification.Proofs.IndexedFullSubcategoryFamilyMaps
import RMod.Classification.Instances.ReconstructionMappedTripleComponents
import RMod.Classification.Proofs.IsoEqualityMaps

/-!
# The product-index comparisons commute with the actual mapped triple maps

Equality of the two product indices identifies both selected component
functors. Naturality of that equality compares the mapped source
associator with the component comparison used to extract omega, and
compares the two presentations of the right triple inclusion.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (A C : PiSuperfusion.{0, 0}) (hC : ReferenceProperty C.data)
  (X Y Z : LinearCategory A.toWeaklyPointedSuperfusion)
  (g h k : SimpleOrbit A.toWeaklyPointedSuperfusion)

theorem reconstructionComponentAssociator_index :
    C.data.comp
      ((reconstructionComponentRealization A C hC ((g * h) * k)).map
        (reconstructionTripleAssociatorAtLeft A X Y Z g h k))
      (IsoData.ofEq C.toWeaklyPointedSuperfusion.data
        (reconstructionTripleRightRealization_index A C hC X Y Z g h k)).hom =
    (componentMappedTripleAssociator (reconstructionComponentSystem A C hC)
      (simpleOrbitRepresentative_mul A.toWeaklyPointedSuperfusion) (reconstruction_target_product A C hC)
      g h k ((reconstructionSourceEquivalence A).inverse.obj X g)
        ((reconstructionSourceEquivalence A).inverse.obj Y h)
        ((reconstructionSourceEquivalence A).inverse.obj Z k)).hom := by
  have hn := indexedFullSubcategoryFunctor_eq_naturality
    (fun q => InHomogeneousSpan A.toWeaklyPointedSuperfusion
      (simpleOrbitRepresentative A.toWeaklyPointedSuperfusion q).data.object)
    (reconstructionComponentRealization A C hC) (mul_assoc g h k)
    (reconstructionTripleLeftSpan A X Y Z g h k).property
    (reconstructionTripleRightSpanAtLeft A X Y Z g h k).property
    (reconstructionTripleLeftSpanAtRight A X Y Z g h k).property
    (reconstructionTripleRightSpan A X Y Z g h k).property
    (reconstructionTripleAssociatorAtLeft A X Y Z g h k).hom
    (reconstructionTripleLeftRealization_index A C hC X Y Z g h k)
    (reconstructionTripleRightRealization_index A C hC X Y Z g h k)
  simp only [linear_eqToHom_eq_ofEq] at hn
  exact hn.trans (reconstructionComponentAssociator_hom A C hC X Y Z g h k).symm

theorem reconstructionMappedTripleRightInclusion_index :
    C.data.comp
      ((reconstructionComponentRealization A C hC ((g * h) * k)).map
        (reconstructionTripleRightInclusionAtLeft A X Y Z g h k))
      (IsoData.ofEq C.toWeaklyPointedSuperfusion.data
        (congrArg (fun j => (((reconstructionUnderlyingEquivalence A C hC).functor.obj
          (A.data.tensorObj X (A.data.tensorObj Y Z))) j).val) (mul_assoc g h k))).hom =
    C.data.comp (IsoData.ofEq C.toWeaklyPointedSuperfusion.data
      (reconstructionTripleRightRealization_index A C hC X Y Z g h k)).hom
      (reconstructionMappedTripleRightInclusion A C hC X Y Z g h k) := by
  let T : LinearCategory A.toWeaklyPointedSuperfusion := A.data.tensorObj X (A.data.tensorObj Y Z)
  let i : A.data.Hom (reconstructionTripleRightSpan A X Y Z g h k).obj T :=
    A.data.tensorHom ((reconstructionSourceBicone A X).ι g) ((reconstructionTensorBicone A Y Z).ι (h, k))
  have hn := indexedFullSubcategoryFunctor_family_naturality
    (fun q => InHomogeneousSpan A.toWeaklyPointedSuperfusion
      (simpleOrbitRepresentative A.toWeaklyPointedSuperfusion q).data.object)
    (reconstructionComponentRealization A C hC) (mul_assoc g h k)
    (reconstructionTripleRightSpanAtLeft A X Y Z g h k).property
    (reconstructionTripleRightSpan A X Y Z g h k).property
    ((reconstructionSourceEquivalence A).inverse.obj T)
    (fun j => A.data.comp i ((reconstructionSourceBicone A T).π j))
    (reconstructionTripleRightRealization_index A C hC X Y Z g h k)
  simp only [linear_eqToHom_eq_ofEq] at hn
  exact hn

end RMod.Classification
