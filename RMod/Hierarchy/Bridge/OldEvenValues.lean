import RMod.Hierarchy.Bridge.OldEquivalenceData

/-!
# Evaluating even morphisms in the old presentation

These formulas expose the preserved maps without unfolding the graded
line implementation in each monoidal coherence proof.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.MonoidalCategory
namespace RMod.Legacy.Hierarchy
variable (C : WeaklyPointedSuperfusion.{0, 0})

def oldValue {X Y : Even (ofOldSupercategory C)} (f : X ⟶ Y) : C.data.Hom X Y :=
  (evenHomEquiv C X Y f).hom

theorem oldValue_comp {X Y Z : Even (ofOldSupercategory C)} (f : X ⟶ Y) (g : Y ⟶ Z) :
    oldValue C (f ≫ g) = C.data.comp (oldValue C f) (oldValue C g) :=
  congrArg (fun h : oldEvenObj C X ⟶ oldEvenObj C Z => h.hom) (evenHomEquiv_comp C X Y Z f g)

theorem oldValue_id (X : Even (ofOldSupercategory C)) : oldValue C (𝟙 X) = C.data.id X :=
  congrArg (fun h : oldEvenObj C X ⟶ oldEvenObj C X => h.hom) (evenHomEquiv_id C X)

theorem oldValue_tensor {X X' Y Y' : Even (ofOldSupercategory C)} (f : X ⟶ X') (g : Y ⟶ Y') :
    oldValue C (f ⊗ₘ g) = C.data.tensorHom (oldValue C f) (oldValue C g) :=
  congrArg (fun h : oldEvenObj C (C.data.tensorObj X Y) ⟶
    oldEvenObj C (C.data.tensorObj X' Y') => h.hom) (evenHomEquiv_tensor C f g)

theorem oldValue_whiskerRight {X Y : Even (ofOldSupercategory C)} (f : X ⟶ Y)
    (Z : Even (ofOldSupercategory C)) :
    oldValue C (f ▷ Z) = C.data.tensorHom (oldValue C f) (C.data.id Z) := by
  rw [← tensorHom_id, oldValue_tensor, oldValue_id]

theorem oldValue_whiskerLeft (X : Even (ofOldSupercategory C))
    {Y Z : Even (ofOldSupercategory C)} (f : Y ⟶ Z) :
    oldValue C (X ◁ f) = C.data.tensorHom (C.data.id X) (oldValue C f) := by
  rw [← id_tensorHom, oldValue_tensor, oldValue_id]

theorem oldValue_associator (X Y Z : Even (ofOldSupercategory C)) :
    oldValue C (α_ X Y Z).hom = C.data.associatorHom X Y Z :=
  congrArg (fun h : oldEvenObj C _ ⟶ oldEvenObj C _ => h.hom) (evenHomEquiv_associatorHom C X Y Z)

theorem oldValue_leftUnitor (X : Even (ofOldSupercategory C)) :
    oldValue C (λ_ X).hom = C.data.leftUnitorHom X :=
  congrArg (fun h : oldEvenObj C _ ⟶ oldEvenObj C _ => h.hom) (evenHomEquiv_leftHom C X)

theorem oldValue_rightUnitor (X : Even (ofOldSupercategory C)) :
    oldValue C (ρ_ X).hom = C.data.rightUnitorHom X :=
  congrArg (fun h : oldEvenObj C _ ⟶ oldEvenObj C _ => h.hom) (evenHomEquiv_rightHom C X)

theorem oldValue_iso {X Y : C.data.Obj} (f : C.data.Hom X Y) (g : C.data.Hom Y X)
    (hf : C.data.IsHomogeneous 0 f) (hg : C.data.IsHomogeneous 0 g)
    (hfg : C.data.comp f g = C.data.id X) (hgf : C.data.comp g f = C.data.id Y) :
    oldValue C (ofOldEvenIso C f g hf hg hfg hgf).hom = f :=
  ofOldEvenIso_hom C f g hf hg hfg hgf

theorem oldValue_map {C D : WeaklyPointedSuperfusion.{0, 0}} (F : Classification.Superfunctor C D)
    {X Y : Even (ofOldSupercategory C)} (f : X ⟶ Y) :
    oldValue D ((Superfunctor.enriched (ofOldSuperfunctor F)).forget.map f) =
      F.data.map (oldValue C f) := rfl

end RMod.Legacy.Hierarchy
