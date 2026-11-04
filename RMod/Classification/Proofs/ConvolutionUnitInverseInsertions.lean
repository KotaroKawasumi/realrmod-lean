import RMod.Classification.Proofs.ConvolutionUnitInsertions

/-!
# The inverse unit maps through their surviving inclusions

The inverse of the actual unitor is its inverse normalized block followed
by the matching convolution inclusion. This keeps the maps used in the
normalized duality snakes explicit.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory CategoryTheory.Limits

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData) (ht : TwistLaws t)

theorem convolutionLeftUnitor_inverse_inclusion (X : PullbackObj C t) (k : t.group) :
    (convolutionLeftUnitorData C hC t ht X k).inv =
      C.comp (convolutionLeftUnitBlock C hC t ht X k).inv.hom
        (convolutionInclusion C hC t (pullbackUnitObj C hC t) X k 1) := by
  have he : (convolutionLeftUnitorEvenIso C hC t ht X k).inv =
      (convolutionLeftUnitBlock C hC t ht X k).inv ≫
        convolutionInclusionEven C hC t (pullbackUnitObj C hC t) X k 1 := by
    simp only [convolutionLeftUnitorEvenIso, convolutionLeftUnitorEvenIsoOfParity, Iso.trans_inv, convolutionInclusionEven,
      biproductSingleIso, Category.assoc, convolutionLeftUnitBlock]
  exact congrArg (fun f => f.hom) he

theorem convolutionRightUnitor_inverse_inclusion (X : PullbackObj C t) (k : t.group) :
    (convolutionRightUnitorData C hC t ht X k).inv =
      C.comp (convolutionRightUnitBlock C hC t ht X k).inv.hom
        (convolutionInclusion C hC t X (pullbackUnitObj C hC t) k k) := by
  have he : (convolutionRightUnitorEvenIso C hC t ht X k).inv =
      (convolutionRightUnitBlock C hC t ht X k).inv ≫
        convolutionInclusionEven C hC t X (pullbackUnitObj C hC t) k k := by
    simp only [convolutionRightUnitorEvenIso, convolutionRightUnitorEvenIsoOfParity, Iso.trans_inv, convolutionInclusionEven,
      biproductSingleIso, Category.assoc, convolutionRightUnitBlock]
  exact congrArg (fun f => f.hom) he

end RMod.Classification
