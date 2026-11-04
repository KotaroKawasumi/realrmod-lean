import RMod.Classification.Instances.ConvolutionInsertions
import RMod.Classification.Proofs.IsoCalculus

/-!
# Scalar comparisons on the actual convolution objects

A nonzero scalar on each binary degree gives an even automorphism of the
chosen convolution. The inverse uses the reciprocal on each summand.
The construction passes through the existing biproduct comparison and
retains the original chosen finite-sum object on both sides.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory CategoryTheory.Limits

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData)
  (beta : t.group → t.group → ℝˣ)

noncomputable def convolutionScalarBlockEvenIso (X Y : PullbackObj C t) (k g : t.group) :
    convolutionEvenFamily C hC t X Y k g ≅ convolutionEvenFamily C hC t X Y k g :=
  IsoData.toEvenIso ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩
    ((IsoData.refl C.toWeaklyPointedSuperfusionData (twistSummand C t X Y g (g⁻¹ * k))).scale
      C.toWeaklyPointedSuperfusionData (beta g (g⁻¹ * k)))
    ((EvenIsoLaws.refl hC.toWeaklyPointedSuperfusionLaws _).scale
      hC.toWeaklyPointedSuperfusionLaws (beta g (g⁻¹ * k)))

noncomputable def convolutionScalarEvenIso (X Y : PullbackObj C t) (k : t.group) :
    referenceEvenObj C hC (convolutionObj C hC t X Y k).val ≅
      referenceEvenObj C hC (convolutionObj C hC t X Y k).val :=
  convolutionEvenIso C hC t X Y k ≪≫
    biproduct.mapIso (convolutionScalarBlockEvenIso C hC t beta X Y k) ≪≫
      (convolutionEvenIso C hC t X Y k).symm

noncomputable def convolutionScalarData (X Y : PullbackObj C t) (k : t.group) :
    IsoData C.toWeaklyPointedSuperfusionData (convolutionObj C hC t X Y k).val
      (convolutionObj C hC t X Y k).val :=
  IsoData.ofEvenIso ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩
    (convolutionScalarEvenIso C hC t beta X Y k)

end RMod.Classification
