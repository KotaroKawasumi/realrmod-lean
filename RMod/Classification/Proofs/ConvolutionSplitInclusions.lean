import RMod.Classification.Instances.ConvolutionFourInsertions
import RMod.Classification.Proofs.ConvolutionInsertions
import Mathlib.CategoryTheory.Functor.EpiMono

/-!
# Convolution inclusions are split monomorphisms

The specified binary projections split the inclusions. Tensor functors
and composition preserve this property, so the nested triple and fourfold
inclusions can be cancelled after comparing actual coherence routes.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory CategoryTheory.MonoidalCategory

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData)

instance convolutionInclusionEven_isSplitMono (X Y : PullbackObj C t) (k g : t.group) :
    IsSplitMono (convolutionInclusionEven C hC t X Y k g) :=
  IsSplitMono.mk'
    { retraction := convolutionProjectionEven C hC t X Y k g
      id := by
        apply WideSubcategory.hom_ext
        exact convolutionInclusion_projection C hC t X Y k g }

instance convolutionRightInsertionEven_isSplitMono
    (X Y Z : PullbackObj C t) (k g h : t.group) :
    IsSplitMono (convolutionRightInsertionEven C hC t X Y Z k g h) := by
  unfold convolutionRightInsertionEven
  change IsSplitMono
    (((tensoringRight (ReferenceEvenCategory C hC)).obj
      (referenceEvenObj C hC (C.pi.factor (t.nu g (g⁻¹ * k))))).map
      (((tensoringLeft (ReferenceEvenCategory C hC)).obj
        (referenceEvenObj C hC (X g).val)).map
        (convolutionInclusionEven C hC t Y Z (g⁻¹ * k) h)) ≫
      convolutionInclusionEven C hC t X (convolutionObj C hC t Y Z) k g)
  exact IsSplitMono.mk'
    ((((convolutionInclusionEven_isSplitMono C hC t Y Z (g⁻¹ * k) h).exists_splitMono.some.map
      ((tensoringLeft (ReferenceEvenCategory C hC)).obj (referenceEvenObj C hC (X g).val))).map
        ((tensoringRight (ReferenceEvenCategory C hC)).obj
          (referenceEvenObj C hC (C.pi.factor (t.nu g (g⁻¹ * k)))))).comp
      (convolutionInclusionEven_isSplitMono C hC t X (convolutionObj C hC t Y Z) k g).exists_splitMono.some)

instance convolutionFourRightInsertion_isSplitMono
    (W X Y Z : PullbackObj C t) (k a b c : t.group) :
    IsSplitMono (convolutionFourRightInsertion C hC t W X Y Z k a b c) := by
  unfold convolutionFourRightInsertion
  change IsSplitMono
    (((tensoringRight (ReferenceEvenCategory C hC)).obj
      (referenceEvenObj C hC (C.pi.factor (t.nu a (a⁻¹ * k))))).map
      (((tensoringLeft (ReferenceEvenCategory C hC)).obj
        (referenceEvenObj C hC (W a).val)).map
        (convolutionRightInsertionEven C hC t X Y Z (a⁻¹ * k) b c)) ≫
      convolutionInclusionEven C hC t W (convolutionObj C hC t X (convolutionObj C hC t Y Z)) k a)
  exact IsSplitMono.mk'
    ((((convolutionRightInsertionEven_isSplitMono C hC t X Y Z (a⁻¹ * k) b c).exists_splitMono.some.map
      ((tensoringLeft (ReferenceEvenCategory C hC)).obj (referenceEvenObj C hC (W a).val))).map
        ((tensoringRight (ReferenceEvenCategory C hC)).obj
          (referenceEvenObj C hC (C.pi.factor (t.nu a (a⁻¹ * k)))))).comp
      (convolutionInclusionEven_isSplitMono C hC t W (convolutionObj C hC t X (convolutionObj C hC t Y Z)) k a).exists_splitMono.some)

end RMod.Classification
