import RMod.Classification.Instances.PullbackSupercategory
import RMod.Classification.Instances.ConvolutionAssociatorOfParity
import RMod.Classification.Instances.ConvolutionUnitorsOfParity
import RMod.Classification.Proofs.ConvolutionMaps

/-!
# The even convolution structure before scalar coherence

The degree-zero category already exists for every twist data. Normalized
parity constructs its tensor, unit, and structural isomorphisms. This is
Mathlib's formation structure only; no pentagon or triangle is asserted.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory Superfusion.Category

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData)
  (hν : ∀ g h k : t.group, t.nu g h + t.nu (g * h) k = t.nu h k + t.nu g (h * k))
  (hνL : ∀ g : t.group, t.nu 1 g = 0) (hνR : ∀ g : t.group, t.nu g 1 = 0)

@[implicit_reducible]
noncomputable def convolutionEvenMonoidalStructOfParity :
    MonoidalCategoryStruct (EvenSubcategory ℝ (PullbackCategory C hC t)) where
  tensorObj X Y := evenObj ℝ _ (convolutionObj C hC t X.obj Y.obj)
  tensorHom f g := ⟨convolutionHom C hC t f.hom g.hom,
    by
      change ∀ q, C.IsHomogeneous 0 (convolutionHom C hC t f.hom g.hom q)
      simpa only [zero_add] using convolutionHom_grade C hC t f.hom g.hom 0 0 f.property g.property⟩
  whiskerLeft X {_ _} f := ⟨convolutionHom C hC t (fun q => C.id (X.obj q).val) f.hom,
    by
      change ∀ q, C.IsHomogeneous 0 (convolutionHom C hC t (fun r => C.id (X.obj r).val) f.hom q)
      simpa only [zero_add] using convolutionHom_grade C hC t _ f.hom 0 0
        (fun q => hC.id_even (X.obj q).val) f.property⟩
  whiskerRight {_ _} f Y := ⟨convolutionHom C hC t f.hom (fun q => C.id (Y.obj q).val),
    by
      change ∀ q, C.IsHomogeneous 0 (convolutionHom C hC t f.hom (fun r => C.id (Y.obj r).val) q)
      simpa only [add_zero] using convolutionHom_grade C hC t f.hom _ 0 0
        f.property (fun q => hC.id_even (Y.obj q).val)⟩
  tensorUnit := evenObj ℝ _ (pullbackUnitObj C hC t)
  associator X Y Z :=
    { hom := ⟨fun q => (convolutionAssociatorEvenIsoOfParity C hC t hν X.obj Y.obj Z.obj q).hom.hom,
        fun q => (convolutionAssociatorEvenIsoOfParity C hC t hν X.obj Y.obj Z.obj q).hom.property⟩
      inv := ⟨fun q => (convolutionAssociatorEvenIsoOfParity C hC t hν X.obj Y.obj Z.obj q).inv.hom,
        fun q => (convolutionAssociatorEvenIsoOfParity C hC t hν X.obj Y.obj Z.obj q).inv.property⟩
      hom_inv_id := by
        apply WideSubcategory.hom_ext
        funext q
        exact congrArg (fun f => f.hom)
          (convolutionAssociatorEvenIsoOfParity C hC t hν X.obj Y.obj Z.obj q).hom_inv_id
      inv_hom_id := by
        apply WideSubcategory.hom_ext
        funext q
        exact congrArg (fun f => f.hom)
          (convolutionAssociatorEvenIsoOfParity C hC t hν X.obj Y.obj Z.obj q).inv_hom_id }
  leftUnitor X :=
    { hom := ⟨fun q => (convolutionLeftUnitorEvenIsoOfParity C hC t hνL X.obj q).hom.hom,
        fun q => (convolutionLeftUnitorEvenIsoOfParity C hC t hνL X.obj q).hom.property⟩
      inv := ⟨fun q => (convolutionLeftUnitorEvenIsoOfParity C hC t hνL X.obj q).inv.hom,
        fun q => (convolutionLeftUnitorEvenIsoOfParity C hC t hνL X.obj q).inv.property⟩
      hom_inv_id := by
        apply WideSubcategory.hom_ext
        funext q
        exact congrArg (fun f => f.hom)
          (convolutionLeftUnitorEvenIsoOfParity C hC t hνL X.obj q).hom_inv_id
      inv_hom_id := by
        apply WideSubcategory.hom_ext
        funext q
        exact congrArg (fun f => f.hom)
          (convolutionLeftUnitorEvenIsoOfParity C hC t hνL X.obj q).inv_hom_id }
  rightUnitor X :=
    { hom := ⟨fun q => (convolutionRightUnitorEvenIsoOfParity C hC t hνR X.obj q).hom.hom,
        fun q => (convolutionRightUnitorEvenIsoOfParity C hC t hνR X.obj q).hom.property⟩
      inv := ⟨fun q => (convolutionRightUnitorEvenIsoOfParity C hC t hνR X.obj q).inv.hom,
        fun q => (convolutionRightUnitorEvenIsoOfParity C hC t hνR X.obj q).inv.property⟩
      hom_inv_id := by
        apply WideSubcategory.hom_ext
        funext q
        exact congrArg (fun f => f.hom)
          (convolutionRightUnitorEvenIsoOfParity C hC t hνR X.obj q).hom_inv_id
      inv_hom_id := by
        apply WideSubcategory.hom_ext
        funext q
        exact congrArg (fun f => f.hom)
          (convolutionRightUnitorEvenIsoOfParity C hC t hνR X.obj q).inv_hom_id }

end RMod.Classification
