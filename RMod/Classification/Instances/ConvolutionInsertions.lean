import RMod.Classification.Instances.ConvolutionBiproduct

/-!
# Group-indexed summand maps in the actual convolution

The chosen finite sum is compared with Mathlib's group-indexed biproduct.
Its canonical inclusions and projections are transported back along that
fixed comparison. The raw maps are their underlying even morphisms, so
they act on the original convolution object and full graded Hom spaces.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory CategoryTheory.Limits

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData)

noncomputable def convolutionInclusionEven (X Y : PullbackObj C t) (k g : t.group) :
    convolutionEvenFamily C hC t X Y k g ⟶ referenceEvenObj C hC (convolutionObj C hC t X Y k).val :=
  biproduct.ι (convolutionEvenFamily C hC t X Y k) g ≫ (convolutionEvenIso C hC t X Y k).inv

noncomputable def convolutionProjectionEven (X Y : PullbackObj C t) (k g : t.group) :
    referenceEvenObj C hC (convolutionObj C hC t X Y k).val ⟶ convolutionEvenFamily C hC t X Y k g :=
  (convolutionEvenIso C hC t X Y k).hom ≫ biproduct.π (convolutionEvenFamily C hC t X Y k) g

noncomputable def convolutionInclusion (X Y : PullbackObj C t) (k g : t.group) :
    C.Hom (twistSummand C t X Y g (g⁻¹ * k)) (convolutionObj C hC t X Y k).val :=
  (convolutionInclusionEven C hC t X Y k g).hom

noncomputable def convolutionProjection (X Y : PullbackObj C t) (k g : t.group) :
    C.Hom (convolutionObj C hC t X Y k).val (twistSummand C t X Y g (g⁻¹ * k)) :=
  (convolutionProjectionEven C hC t X Y k g).hom

end RMod.Classification
