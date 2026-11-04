import RMod.Classification.Instances.ConvolutionInsertions
import RMod.Classification.Instances.ConvolutionExpansion

/-!
# Inclusions of the actual threefold convolution summands

Both parenthesizations retain their two parity factors in their original
positions. The outer group index is fixed; the two independent labels
are precisely the labels used by the iterated biproduct expansions.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory CategoryTheory.Limits MonoidalCategory

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData)

noncomputable def convolutionLeftInsertionEven (X Y Z : PullbackObj C t) (k a g : t.group) :
    convolutionLeftFamily C hC t X Y Z k a g ⟶
      referenceEvenObj C hC (convolutionObj C hC t (convolutionObj C hC t X Y) Z k).val :=
  ((convolutionInclusionEven C hC t X Y a g ▷ referenceEvenObj C hC (Z (a⁻¹ * k)).val) ▷
    referenceEvenObj C hC (C.pi.factor (t.nu a (a⁻¹ * k)))) ≫
      convolutionInclusionEven C hC t (convolutionObj C hC t X Y) Z k a

noncomputable def convolutionRightInsertionEven (X Y Z : PullbackObj C t) (k g h : t.group) :
    convolutionRightFamily C hC t X Y Z k g h ⟶
      referenceEvenObj C hC (convolutionObj C hC t X (convolutionObj C hC t Y Z) k).val :=
  ((referenceEvenObj C hC (X g).val ◁ convolutionInclusionEven C hC t Y Z (g⁻¹ * k) h) ▷
    referenceEvenObj C hC (C.pi.factor (t.nu g (g⁻¹ * k)))) ≫
      convolutionInclusionEven C hC t X (convolutionObj C hC t Y Z) k g

end RMod.Classification
