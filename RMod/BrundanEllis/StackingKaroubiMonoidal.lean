import RMod.BrundanEllis.StackingKaroubiCoherence

/-! The ordinary monoidal structure extends to even idempotent completion.
All operations are the original operations restricted to tensor idempotents;
associativity and unit coherence follow by cutting the original diagrams. -/
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Idempotents
namespace RMod.BrundanEllis.Stacking.KaroubiTensor
variable {C : Type} [Category C] [MonoidalCategory C]

instance monoidalStruct : MonoidalCategoryStruct (Karoubi C) where
  tensorObj := objectTensor
  whiskerLeft P _ _ g := mapTensor (𝟙 P) g
  whiskerRight f Q := mapTensor f (𝟙 Q)
  tensorHom := mapTensor
  tensorUnit := ((𝟙_ C : C) : Karoubi C)
  associator := associator
  leftUnitor := leftUnitor
  rightUnitor := rightUnitor

instance monoidal : MonoidalCategory (Karoubi C) := MonoidalCategory.ofTensorHom
  (id_tensorHom_id := fun _ _ => rfl)
  (id_tensorHom := by intros; rfl)
  (tensorHom_id := by intros; rfl)
  (tensorHom_comp_tensorHom := by
    intro P P' P'' Q Q' Q'' f g f' g'
    apply Karoubi.hom_ext
    exact tensorHom_comp_tensorHom f.f g.f f'.f g'.f)
  (associator_naturality := by
    intro P Q R P' Q' R' f g h
    change mapTensor (mapTensor f g) h ≫ (associator P' Q' R').hom =
      (associator P Q R).hom ≫ mapTensor f (mapTensor g h)
    rw [← cut_hom f, ← cut_hom g, ← cut_hom h]
    simp only [cut_tensor, associator_hom_cut, cut_comp]
    apply Karoubi.hom_ext
    simp only [cut_f, Category.assoc, objectTensor]
    rw [associator_naturality])
  (leftUnitor_naturality := by
    intro P Q f
    change mapTensor (𝟙 (((𝟙_ C : C) : Karoubi C))) f ≫ (leftUnitor Q).hom =
      (leftUnitor P).hom ≫ f
    rw [← cut_hom f, ← cut_id (((𝟙_ C : C) : Karoubi C))]
    simp only [cut_tensor, leftUnitor_hom_cut, cut_comp]
    apply Karoubi.hom_ext
    simp only [cut_f, Category.assoc, objectTensor]
    simp only [id_tensorHom, leftUnitor_naturality])
  (rightUnitor_naturality := by
    intro P Q f
    change mapTensor f (𝟙 (((𝟙_ C : C) : Karoubi C))) ≫ (rightUnitor Q).hom =
      (rightUnitor P).hom ≫ f
    rw [← cut_hom f, ← cut_id (((𝟙_ C : C) : Karoubi C))]
    simp only [cut_tensor, rightUnitor_hom_cut, cut_comp]
    apply Karoubi.hom_ext
    simp only [cut_f, Category.assoc, objectTensor]
    simp only [tensorHom_id, rightUnitor_naturality])
  (pentagon := by
    intro P Q R S
    change mapTensor (associator P Q R).hom (𝟙 S) ≫
        (associator P (objectTensor Q R) S).hom ≫ mapTensor (𝟙 P) (associator Q R S).hom =
      (associator (objectTensor P Q) R S).hom ≫ (associator P Q (objectTensor R S)).hom
    rw [← cut_id P, ← cut_id S]
    simp only [associator_hom_cut, cut_tensor, cut_comp]
    apply Karoubi.hom_ext
    simp only [cut_f, Category.assoc, objectTensor]
    simp only [tensorHom_id, id_tensorHom, pentagon])
  (triangle := by
    intro P Q
    change (associator P (((𝟙_ C : C) : Karoubi C)) Q).hom ≫
        mapTensor (𝟙 P) (leftUnitor Q).hom = mapTensor (rightUnitor P).hom (𝟙 Q)
    rw [← cut_id P, ← cut_id Q]
    simp only [associator_hom_cut, leftUnitor_hom_cut, rightUnitor_hom_cut, cut_tensor, cut_comp]
    apply Karoubi.hom_ext
    simp only [cut_f, Category.assoc, objectTensor]
    simp only [tensorHom_id, id_tensorHom, triangle])

@[simp] theorem tensorObj_X (P Q : Karoubi C) : (P ⊗ Q).X = P.X ⊗ Q.X := rfl
@[simp] theorem tensorObj_p (P Q : Karoubi C) : (P ⊗ Q).p = P.p ⊗ₘ Q.p := rfl
@[simp] theorem tensorUnit_X : (𝟙_ (Karoubi C)).X = 𝟙_ C := rfl
@[simp] theorem tensorUnit_p : (𝟙_ (Karoubi C)).p = 𝟙 (𝟙_ C) := rfl
@[simp] theorem whiskerLeft_f (P : Karoubi C) {Q R : Karoubi C} (f : Q ⟶ R) :
    (P ◁ f).f = P.p ⊗ₘ f.f := rfl
@[simp] theorem whiskerRight_f {P Q : Karoubi C} (f : P ⟶ Q) (R : Karoubi C) :
    (f ▷ R).f = f.f ⊗ₘ R.p := rfl
@[simp] theorem associator_hom_f (P Q R : Karoubi C) :
    (α_ P Q R).hom.f = ((P.p ⊗ₘ Q.p) ⊗ₘ R.p) ≫ (α_ P.X Q.X R.X).hom := rfl
@[simp] theorem leftUnitor_hom_f (P : Karoubi C) :
    (λ_ P).hom.f = (𝟙 (𝟙_ C) ⊗ₘ P.p) ≫ (λ_ P.X).hom := rfl
@[simp] theorem rightUnitor_hom_f (P : Karoubi C) :
    (ρ_ P).hom.f = (P.p ⊗ₘ 𝟙 (𝟙_ C)) ≫ (ρ_ P.X).hom := rfl

end RMod.BrundanEllis.Stacking.KaroubiTensor
