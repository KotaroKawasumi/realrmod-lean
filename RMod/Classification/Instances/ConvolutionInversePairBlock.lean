import RMod.Classification.Instances.ConvolutionAssociator

/-!
# The associator block for two inverse group degrees

The general block starts at the coordinate g*g⁻¹. Its equality with the
identity changes only that source type. This explicit comparison is useful
when a coevaluation has already entered the identity component.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData) (ht : TwistLaws t)

noncomputable def convolutionInversePairBlock (X Y Z : PullbackObj C t) (k g : t.group) :
    convolutionLeftFamily C hC t X Y Z k 1 g ≅ convolutionRightFamily C hC t X Y Z k g g⁻¹ :=
  eqToIso (congrArg (fun a => convolutionLeftFamily C hC t X Y Z k a g) (mul_inv_cancel g).symm) ≪≫
    convolutionBlockIso C hC t ht X Y Z k g g⁻¹

end RMod.Classification
