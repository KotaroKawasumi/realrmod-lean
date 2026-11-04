import RMod.Classification.Instances.ConvolutionInsertions

/-!
# A fixed summand degree as a pullback family

Fixing the left degree in a binary convolution leaves a family indexed
by its total degree. Component closure supplies its existing pullback
certificate. Its coordinatewise inclusion into the full convolution is
the already chosen inclusion, so naturality can be applied directly to
this family when proving the middle edges of the fourfold pentagon.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData)

def convolutionSummandObj (X Y : PullbackObj C t) (g : t.group) : PullbackObj C t := fun k =>
  ⟨twistSummand C t X Y g (g⁻¹ * k), by
    have h := twistSummand_inComponent C hC t X Y g (g⁻¹ * k)
    simpa only [mul_inv_cancel_left] using h⟩

noncomputable def convolutionSummandInclusion (X Y : PullbackObj C t) (g : t.group) :
    PullbackHom C t (convolutionSummandObj C hC t X Y g) (convolutionObj C hC t X Y) :=
  fun k => convolutionInclusion C hC t X Y k g

end RMod.Classification
