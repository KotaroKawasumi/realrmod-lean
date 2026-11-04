import RMod.Classification.Proofs.ConvolutionFourWhiskerEdgesOfParity
import RMod.Classification.Proofs.ConvolutionFourExt
import RMod.Classification.Proofs.ConvolutionNaturality

/-!
# The two whiskered edges of the fourfold pentagon

For the first and last edges of the long path, a fixed-object tensor
functor carries the exact threefold associator insertion equation to the
fourfold one. The outer convolution map commutes with its inclusion.
-/

set_option autoImplicit false

namespace RMod.Classification

attribute [local implicit_reducible] convolutionFourLeftFamily convolutionFourInnerFamily
  convolutionFourOuterFamily convolutionFourRightFamily convolutionLeftFamily
  convolutionRightFamily convolutionEvenFamily twistSummand

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData)
  (ht : TwistLaws t)

theorem convolutionFourLeftInsertion_first (W X Y Z : PullbackObj C t) (k a b c : t.group) :
    C.comp (convolutionFourLeftInsertion C hC t W X Y Z k a (b * c) b).hom
      (convolutionHom C hC t (fun g => (convolutionAssociatorData C hC t ht W X Y g).hom)
        (fun g => C.id (Z g).val) k) =
    C.comp (C.tensorHom (C.tensorHom (convolutionBlockIso C hC t ht W X Y a b c).hom.hom
      (C.id (Z (a⁻¹ * k)).val)) (C.id (C.pi.factor (t.nu a (a⁻¹ * k)))))
      (convolutionFourInnerInsertion C hC t W X Y Z k a b c).hom :=
  convolutionFourLeftInsertion_firstOfParity C hC t ht.normalizer_parity W X Y Z k a b c

theorem convolutionFourOuterInsertion_last (W X Y Z : PullbackObj C t) (k a b c : t.group) :
    C.comp (convolutionFourOuterInsertion C hC t W X Y Z k a (b * c) b).hom
      (convolutionHom C hC t (fun g => C.id (W g).val)
        (fun g => (convolutionAssociatorData C hC t ht X Y Z g).hom) k) =
    C.comp (C.tensorHom (C.tensorHom (C.id (W a).val)
      (convolutionBlockIso C hC t ht X Y Z (a⁻¹ * k) b c).hom.hom)
      (C.id (C.pi.factor (t.nu a (a⁻¹ * k)))))
      (convolutionFourRightInsertion C hC t W X Y Z k a b c).hom :=
  convolutionFourOuterInsertion_lastOfParity C hC t ht.normalizer_parity W X Y Z k a b c

end RMod.Classification
