import RMod.Classification.Proofs.ConvolutionUnitBlockNaturality
import RMod.Classification.Proofs.ConvolutionUnitInsertions
import RMod.Classification.Proofs.ConvolutionUnitInsertionsOfParity
import RMod.Classification.Instances.TwistedPullbackData

/-!
# Naturality of the specified convolution unitors

Convolution maps commute with every chosen projection. In particular,
the surviving unit projection reduces the entire naturality square to
the normalized unit block. This argument applies to arbitrary morphisms
without imposing a grading hypothesis.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData)
  (ht : TwistLaws t) {X Y : PullbackObj C t}

theorem convolutionLeftUnitorOfParity_naturality
    (hνL : ∀ g : t.group, t.nu 1 g = 0) (f : PullbackHom C t X Y) (k : t.group) :
    C.comp (convolutionHom C hC t (fun a => C.id (pullbackUnitObj C hC t a).val) f k)
      (convolutionLeftUnitorDataOfParity C hC t hνL Y k).hom =
        C.comp (convolutionLeftUnitorDataOfParity C hC t hνL X k).hom (f k) := by
  rw [convolutionLeftUnitor_projectionOfParity, convolutionLeftUnitor_projectionOfParity, ← hC.comp_assoc,
    convolutionMap_projection, hC.comp_assoc, convolutionLeftUnitBlockOfParity_naturality]
  exact (hC.comp_assoc _ _ _).symm

theorem convolutionLeftUnitor_naturality (f : PullbackHom C t X Y) (k : t.group) :
    C.comp (convolutionHom C hC t (fun a => C.id (pullbackUnitObj C hC t a).val) f k)
      (convolutionLeftUnitorData C hC t ht Y k).hom =
        C.comp (convolutionLeftUnitorData C hC t ht X k).hom (f k) :=
  convolutionLeftUnitorOfParity_naturality C hC t ht.nu_one_left f k

theorem convolutionRightUnitorOfParity_naturality
    (hνR : ∀ g : t.group, t.nu g 1 = 0) (f : PullbackHom C t X Y) (k : t.group) :
    C.comp (convolutionHom C hC t f (fun a => C.id (pullbackUnitObj C hC t a).val) k)
      (convolutionRightUnitorDataOfParity C hC t hνR Y k).hom =
        C.comp (convolutionRightUnitorDataOfParity C hC t hνR X k).hom (f k) := by
  rw [convolutionRightUnitor_projectionOfParity, convolutionRightUnitor_projectionOfParity, ← hC.comp_assoc,
    convolutionMap_projection, hC.comp_assoc, convolutionRightUnitBlockOfParity_naturality]
  exact (hC.comp_assoc _ _ _).symm

theorem convolutionRightUnitor_naturality (f : PullbackHom C t X Y) (k : t.group) :
    C.comp (convolutionHom C hC t f (fun a => C.id (pullbackUnitObj C hC t a).val) k)
      (convolutionRightUnitorData C hC t ht Y k).hom =
        C.comp (convolutionRightUnitorData C hC t ht X k).hom (f k) :=
  convolutionRightUnitorOfParity_naturality C hC t ht.nu_one_right f k

theorem twistedPullback_left_unitor_naturality
    {X Y : (twistedPullbackData C hC t ht).Obj}
    (f : (twistedPullbackData C hC t ht).Hom X Y) :
    let D := twistedPullbackData C hC t ht
    D.comp (D.tensorHom (D.id D.tensorUnit) f) (D.leftUnitorHom Y) =
      D.comp (D.leftUnitorHom X) f := by
  funext k
  exact convolutionLeftUnitor_naturality C hC t ht f k

theorem twistedPullback_right_unitor_naturality
    {X Y : (twistedPullbackData C hC t ht).Obj}
    (f : (twistedPullbackData C hC t ht).Hom X Y) :
    let D := twistedPullbackData C hC t ht
    D.comp (D.tensorHom f (D.id D.tensorUnit)) (D.rightUnitorHom Y) =
      D.comp (D.rightUnitorHom X) f := by
  funext k
  exact convolutionRightUnitor_naturality C hC t ht f k

end RMod.Classification
