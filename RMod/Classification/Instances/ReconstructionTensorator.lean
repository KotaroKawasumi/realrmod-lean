import RMod.Classification.Instances.ReconstructionTensorBlock
import RMod.Classification.Proofs.ReconstructionTensorOutputIndex
import RMod.Classification.Proofs.ReconstructionMappedTensorEvenBicone

/-!
# The actual tensorator of the global reconstruction functor

First identify the chosen convolution sum with its indexed even
biproduct. Apply the even binary comparison to each summand, retaining
the product-degree equality map. Finally use the mapped component
presentation of F(X tensor Y). The inverse follows these three specified
isomorphisms in reverse, so both maps are actual construction data.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory CategoryTheory.Limits

variable (A C : PiSuperfusion.{0, 0}) (hC : ReferenceProperty C.data)
  (X Y : LinearCategory A.toWeaklyPointedSuperfusion)

noncomputable def reconstructionConvolutionBlockIso (k g : SimpleOrbit A.toWeaklyPointedSuperfusion) :
    convolutionEvenFamily C.data hC (reconstructionTwistData A C hC)
      ((reconstructionUnderlyingEquivalence A C hC).functor.obj X)
      ((reconstructionUnderlyingEquivalence A C hC).functor.obj Y) k g ≅
    referenceEvenObj C.data hC ((reconstructionComponentRealization A C hC k).obj
      (reconstructionTensorOutputSpan A X Y k g)) :=
  reconstructionTensorBlock A C hC X Y g (g⁻¹ * k) ≪≫
    eqToIso (congrArg (referenceEvenObj C.data hC)
      (reconstructionTensorOutputRealization_obj A C hC X Y k g).symm)

noncomputable def reconstructionTensoratorEvenIso (k : SimpleOrbit A.toWeaklyPointedSuperfusion) :
    referenceEvenObj C.data hC (convolutionObj C.data hC (reconstructionTwistData A C hC)
      ((reconstructionUnderlyingEquivalence A C hC).functor.obj X)
      ((reconstructionUnderlyingEquivalence A C hC).functor.obj Y) k).val ≅
    referenceEvenObj C.data hC
      (((reconstructionUnderlyingEquivalence A C hC).functor.obj (A.data.tensorObj X Y)) k).val :=
  convolutionEvenIso C.data hC (reconstructionTwistData A C hC)
      ((reconstructionUnderlyingEquivalence A C hC).functor.obj X)
      ((reconstructionUnderlyingEquivalence A C hC).functor.obj Y) k ≪≫
    biproduct.mapIso (reconstructionConvolutionBlockIso A C hC X Y k) ≪≫
    (biproduct.uniqueUpToIso _ (reconstructionMappedTensorEvenBicone_isBilimit A C hC X Y k)).symm

noncomputable def reconstructionTensoratorData (k : SimpleOrbit A.toWeaklyPointedSuperfusion) :
    IsoData C.toWeaklyPointedSuperfusion.data
      (convolutionObj C.data hC (reconstructionTwistData A C hC)
        ((reconstructionUnderlyingEquivalence A C hC).functor.obj X)
        ((reconstructionUnderlyingEquivalence A C hC).functor.obj Y) k).val
      (((reconstructionUnderlyingEquivalence A C hC).functor.obj (A.data.tensorObj X Y)) k).val :=
  IsoData.ofEvenIso C.toWeaklyPointedSuperfusion (reconstructionTensoratorEvenIso A C hC X Y k)

end RMod.Classification
