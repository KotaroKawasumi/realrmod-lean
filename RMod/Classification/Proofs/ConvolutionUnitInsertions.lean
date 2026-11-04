import RMod.Classification.Instances.ConvolutionUnitors
import RMod.Classification.Proofs.ConvolutionUnitInsertionsOfParity

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
  (ht : TwistLaws t)

theorem convolutionLeftUnitor_projection (X : PullbackObj C t) (k : t.group) :
    (convolutionLeftUnitorData C hC t ht X k).hom =
      C.comp (convolutionProjection C hC t (pullbackUnitObj C hC t) X k 1)
        (convolutionLeftUnitBlock C hC t ht X k).hom.hom :=
  convolutionLeftUnitor_projectionOfParity C hC t ht.nu_one_left X k

theorem convolutionRightUnitor_projection (X : PullbackObj C t) (k : t.group) :
    (convolutionRightUnitorData C hC t ht X k).hom =
      C.comp (convolutionProjection C hC t X (pullbackUnitObj C hC t) k k)
        (convolutionRightUnitBlock C hC t ht X k).hom.hom :=
  convolutionRightUnitor_projectionOfParity C hC t ht.nu_one_right X k

theorem convolutionLeftUnitor_inclusion (X : PullbackObj C t) (k : t.group) :
    C.comp (convolutionInclusion C hC t (pullbackUnitObj C hC t) X k 1)
      (convolutionLeftUnitorData C hC t ht X k).hom =
        (convolutionLeftUnitBlock C hC t ht X k).hom.hom :=
  convolutionLeftUnitor_inclusionOfParity C hC t ht.nu_one_left X k

theorem convolutionRightUnitor_inclusion (X : PullbackObj C t) (k : t.group) :
    C.comp (convolutionInclusion C hC t X (pullbackUnitObj C hC t) k k)
      (convolutionRightUnitorData C hC t ht X k).hom =
        (convolutionRightUnitBlock C hC t ht X k).hom.hom :=
  convolutionRightUnitor_inclusionOfParity C hC t ht.nu_one_right X k

end RMod.Classification
