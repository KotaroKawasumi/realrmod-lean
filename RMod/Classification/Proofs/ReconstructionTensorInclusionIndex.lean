import RMod.Classification.Proofs.ReconstructionTensorBlockFormula
import RMod.Classification.Instances.ReconstructionMappedTripleComponents
import RMod.Classification.Proofs.IndexedFullSubcategoryFamilyMaps
import RMod.Classification.Proofs.IsoEqualityMaps

/-!
# Moving the output index comparison through the mapped tensor inclusion

The mapped source inclusion is a family of maps obtained by projecting
one fixed tensor inclusion to each selected source component. Naturality
of equality in the component index moves the block's equality comparison
to the final image of the tensor object.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (A C : PiSuperfusion.{0, 0}) (hC : ReferenceProperty C.data)
  (X Y : LinearCategory A.toWeaklyPointedSuperfusion)
  (k g : SimpleOrbit A.toWeaklyPointedSuperfusion)

theorem reconstructionMappedTensorInclusion_index :
    C.data.comp
      (IsoData.ofEq C.toWeaklyPointedSuperfusion.data
        (reconstructionTensorOutputRealization_obj A C hC X Y k g).symm).hom
      ((reconstructionMappedTensorBicone A C hC X Y k).ι g) =
    C.data.comp (reconstructionMappedTensorSpanInclusion A C hC X Y g (g⁻¹ * k))
      (IsoData.ofEq C.toWeaklyPointedSuperfusion.data
        (congrArg (fun j => (((reconstructionUnderlyingEquivalence A C hC).functor.obj
          (A.data.tensorObj X Y)) j).val) (mul_inv_cancel_left g k))).hom := by
  have hn := indexedFullSubcategoryFunctor_family_naturality
    (fun q => InHomogeneousSpan A.toWeaklyPointedSuperfusion
      (simpleOrbitRepresentative A.toWeaklyPointedSuperfusion q).data.object)
    (reconstructionComponentRealization A C hC) (mul_inv_cancel_left g k)
    (reconstructionTensorSpanObject A X Y g (g⁻¹ * k)).property
    (reconstructionTensorOutputSpan A X Y k g).property
    ((reconstructionSourceEquivalence A).inverse.obj (A.data.tensorObj X Y))
    (fun j => A.data.comp ((reconstructionTensorBicone A X Y).ι (g, g⁻¹ * k))
      ((reconstructionSourceBicone A (A.data.tensorObj X Y)).π j))
    (reconstructionTensorOutputRealization_obj A C hC X Y k g).symm
  simp only [linear_eqToHom_eq_ofEq] at hn
  exact hn.symm

end RMod.Classification
