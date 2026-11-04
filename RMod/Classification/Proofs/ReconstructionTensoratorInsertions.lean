import RMod.Classification.Proofs.ReconstructionTensorator
import RMod.Classification.Instances.ConvolutionInsertions

/-!
# The global tensorator on each actual convolution summand

The chosen convolution comparison cancels against its inverse inclusion.
The biproduct map then applies precisely the selected binary block, and
the final comparison takes the canonical inclusion to the mapped tensor
component inclusion. This fixes the global map on all summands.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory CategoryTheory.Limits

variable (A C : PiSuperfusion.{0, 0}) (hC : ReferenceProperty C.data)
  (X Y : LinearCategory A.toWeaklyPointedSuperfusion)

theorem reconstructionTensoratorEvenIso_inclusion (k g : SimpleOrbit A.toWeaklyPointedSuperfusion) :
    convolutionInclusionEven C.data hC (reconstructionTwistData A C hC)
      ((reconstructionUnderlyingEquivalence A C hC).functor.obj X)
      ((reconstructionUnderlyingEquivalence A C hC).functor.obj Y) k g ≫
      (reconstructionTensoratorEvenIso A C hC X Y k).hom =
    (reconstructionConvolutionBlockIso A C hC X Y k g).hom ≫
      (reconstructionMappedTensorEvenBicone A C hC X Y k).ι g := by
  simp only [convolutionInclusionEven, reconstructionTensoratorEvenIso, Iso.trans_hom,
    Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc, biproduct.mapIso_hom,
    biproduct.ι_map_assoc, biproduct.uniqueUpToIso_inv]
  exact congrArg (fun f => (reconstructionConvolutionBlockIso A C hC X Y k g).hom ≫ f)
    (biproduct.ι_desc (reconstructionMappedTensorEvenBicone A C hC X Y k).ι g)

theorem reconstructionTensorator_inclusion (k g : SimpleOrbit A.toWeaklyPointedSuperfusion) :
    C.data.comp (convolutionInclusion C.data hC (reconstructionTwistData A C hC)
      ((reconstructionUnderlyingEquivalence A C hC).functor.obj X)
      ((reconstructionUnderlyingEquivalence A C hC).functor.obj Y) k g)
      (reconstructionTensoratorData A C hC X Y k).hom =
    C.data.comp (reconstructionConvolutionBlockIso A C hC X Y k g).hom.hom
      ((reconstructionMappedTensorBicone A C hC X Y k).ι g) :=
  congrArg (fun f => f.hom) (reconstructionTensoratorEvenIso_inclusion A C hC X Y k g)

end RMod.Classification
