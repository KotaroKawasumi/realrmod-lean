import RMod.Classification.Instances.ConvolutionUnitorsOfParity
import RMod.Classification.Proofs.ConvolutionInsertions

/-!
# Unit maps on their surviving convolution summands

Each actual unitor is its surviving projection followed by the normalized
unit block. Consequently its composite with the matching inclusion is
exactly that block. These equalities retain the specified maps rather
than merely asserting existence of a unit comparison.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory CategoryTheory.Limits

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData)
  (hνL : ∀ g : t.group, t.nu 1 g = 0) (hνR : ∀ g : t.group, t.nu g 1 = 0)

theorem convolutionLeftUnitor_projectionOfParity (X : PullbackObj C t) (k : t.group) :
    (convolutionLeftUnitorDataOfParity C hC t hνL X k).hom =
      C.comp (convolutionProjection C hC t (pullbackUnitObj C hC t) X k 1)
        (convolutionLeftUnitBlockOfParity C hC t hνL X k).hom.hom := by
  have he : (convolutionLeftUnitorEvenIsoOfParity C hC t hνL X k).hom =
      convolutionProjectionEven C hC t (pullbackUnitObj C hC t) X k 1 ≫
        (convolutionLeftUnitBlockOfParity C hC t hνL X k).hom := by
    simp only [convolutionLeftUnitorEvenIsoOfParity, Iso.trans_hom, convolutionProjectionEven,
      biproductSingleIso, Category.assoc]
  exact congrArg (fun f => f.hom) he

theorem convolutionRightUnitor_projectionOfParity (X : PullbackObj C t) (k : t.group) :
    (convolutionRightUnitorDataOfParity C hC t hνR X k).hom =
      C.comp (convolutionProjection C hC t X (pullbackUnitObj C hC t) k k)
        (convolutionRightUnitBlockOfParity C hC t hνR X k).hom.hom := by
  have he : (convolutionRightUnitorEvenIsoOfParity C hC t hνR X k).hom =
      convolutionProjectionEven C hC t X (pullbackUnitObj C hC t) k k ≫
        (convolutionRightUnitBlockOfParity C hC t hνR X k).hom := by
    simp only [convolutionRightUnitorEvenIsoOfParity, Iso.trans_hom, convolutionProjectionEven,
      biproductSingleIso, Category.assoc]
  exact congrArg (fun f => f.hom) he

theorem convolutionLeftUnitor_inclusionOfParity (X : PullbackObj C t) (k : t.group) :
    C.comp (convolutionInclusion C hC t (pullbackUnitObj C hC t) X k 1)
      (convolutionLeftUnitorDataOfParity C hC t hνL X k).hom =
        (convolutionLeftUnitBlockOfParity C hC t hνL X k).hom.hom := by
  rw [convolutionLeftUnitor_projectionOfParity, ← hC.comp_assoc,
    convolutionInclusion_projection, hC.id_comp]

theorem convolutionRightUnitor_inclusionOfParity (X : PullbackObj C t) (k : t.group) :
    C.comp (convolutionInclusion C hC t X (pullbackUnitObj C hC t) k k)
      (convolutionRightUnitorDataOfParity C hC t hνR X k).hom =
        (convolutionRightUnitBlockOfParity C hC t hνR X k).hom.hom := by
  rw [convolutionRightUnitor_projectionOfParity, ← hC.comp_assoc,
    convolutionInclusion_projection, hC.id_comp]

end RMod.Classification
