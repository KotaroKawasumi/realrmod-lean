import RMod.BrundanEllis.StackingKaroubiInclusion

/-! Monoidal functors act on idempotent corners by applying the original
functor to each projector. Tensor comparisons are the restricted original
comparisons, so their coherence follows by cutting the original diagrams. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Idempotents
namespace RMod.BrundanEllis.Stacking.KaroubiTensor
variable {C D : Type} [Category C] [Category D]

def mapFunctor (F : C ⥤ D) : Karoubi C ⥤ Karoubi D where
  obj P := ⟨F.obj P.X, F.map P.p, by rw [← F.map_comp, P.idem]⟩
  map f := ⟨F.map f.f, by simp only [← F.map_comp]; rw [f.comm]⟩
  map_id P := by apply Karoubi.hom_ext; rfl
  map_comp f g := by apply Karoubi.hom_ext; exact F.map_comp _ _

@[simp] theorem mapFunctor_cut (F : C ⥤ D) {P Q : Karoubi C}
    (f : P.X ⟶ Q.X) (h : P.p ≫ f = f ≫ Q.p) :
    (mapFunctor F).map (cut f h) = cut (F.map f) (by
      change F.map P.p ≫ F.map f = F.map f ≫ F.map Q.p
      rw [← F.map_comp, h, F.map_comp]) := by
  apply Karoubi.hom_ext
  exact F.map_comp _ _

variable [MonoidalCategory C] [MonoidalCategory D]
variable (F : C ⥤ D) [F.Monoidal]

def mapUnitIso : (𝟙_ (Karoubi D)) ≅ (mapFunctor F).obj (𝟙_ (Karoubi C)) :=
  restrictIso (Functor.Monoidal.εIso F) (by simp [mapFunctor])

def mapTensorIso (P Q : Karoubi C) :
    (mapFunctor F).obj P ⊗ (mapFunctor F).obj Q ≅ (mapFunctor F).obj (P ⊗ Q) :=
  restrictIso (Functor.Monoidal.μIso F P.X Q.X) (by
    change (F.map P.p ⊗ₘ F.map Q.p) ≫ _ = _ ≫ F.map (P.p ⊗ₘ Q.p)
    exact Functor.LaxMonoidal.μ_natural F P.p Q.p)

@[simp] theorem mapUnitIso_hom_cut :
    (mapUnitIso F).hom = cut (Functor.LaxMonoidal.ε F) (by
      change (𝟙 _) ≫ _ = _ ≫ F.map (𝟙 _)
      simp) := rfl

@[simp] theorem mapTensorIso_hom_cut (P Q : Karoubi C) :
    (mapTensorIso F P Q).hom = cut (Functor.LaxMonoidal.μ F P.X Q.X) (by
      change (F.map P.p ⊗ₘ F.map Q.p) ≫ _ = _ ≫ F.map (P.p ⊗ₘ Q.p)
      exact Functor.LaxMonoidal.μ_natural F P.p Q.p) := rfl

/-- Restrict the original monoidal comparisons to the image projectors. -/
def mapMonoidal : (mapFunctor F).CoreMonoidal where
  εIso := mapUnitIso F
  μIso := mapTensorIso F
  μIso_hom_natural_left := by
    intros
    apply Karoubi.hom_ext
    simp [mapFunctor, mapTensorIso, Functor.LaxMonoidal.μ_natural,
      ← F.map_comp, tensorHom_comp_tensorHom]
  μIso_hom_natural_right := by
    intros
    apply Karoubi.hom_ext
    simp [mapFunctor, mapTensorIso, Functor.LaxMonoidal.μ_natural,
      ← F.map_comp, tensorHom_comp_tensorHom]
  associativity := by
    intro P Q R
    change mapTensor (mapTensorIso F P Q).hom (𝟙 ((mapFunctor F).obj R)) ≫
        (mapTensorIso F (P ⊗ Q) R).hom ≫ (mapFunctor F).map (associator P Q R).hom =
      (associator ((mapFunctor F).obj P) ((mapFunctor F).obj Q) ((mapFunctor F).obj R)).hom ≫
        mapTensor (𝟙 ((mapFunctor F).obj P)) (mapTensorIso F Q R).hom ≫
          (mapTensorIso F P (Q ⊗ R)).hom
    rw [← cut_id ((mapFunctor F).obj R), ← cut_id ((mapFunctor F).obj P)]
    simp only [mapTensorIso_hom_cut, associator_hom_cut, mapFunctor_cut, cut_tensor, cut_comp]
    apply Karoubi.hom_ext
    simp only [cut_f, objectTensor, mapFunctor,
      tensorHom_id, id_tensorHom, tensorObj_X, Functor.LaxMonoidal.associativity]
  left_unitality := by
    intro P
    change (leftUnitor ((mapFunctor F).obj P)).hom =
      mapTensor (mapUnitIso F).hom (𝟙 ((mapFunctor F).obj P)) ≫
        (mapTensorIso F (𝟙_ (Karoubi C)) P).hom ≫ (mapFunctor F).map (leftUnitor P).hom
    rw [← cut_id ((mapFunctor F).obj P)]
    simp only [leftUnitor_hom_cut, mapUnitIso_hom_cut, mapTensorIso_hom_cut,
      mapFunctor_cut, cut_tensor, cut_comp]
    apply Karoubi.hom_ext
    simp only [cut_f, objectTensor, mapFunctor,
      tensorHom_id, id_tensorHom, tensorUnit_X, Functor.LaxMonoidal.left_unitality]
  right_unitality := by
    intro P
    change (rightUnitor ((mapFunctor F).obj P)).hom =
      mapTensor (𝟙 ((mapFunctor F).obj P)) (mapUnitIso F).hom ≫
        (mapTensorIso F P (𝟙_ (Karoubi C))).hom ≫ (mapFunctor F).map (rightUnitor P).hom
    rw [← cut_id ((mapFunctor F).obj P)]
    simp only [rightUnitor_hom_cut, mapUnitIso_hom_cut, mapTensorIso_hom_cut,
      mapFunctor_cut, cut_tensor, cut_comp]
    apply Karoubi.hom_ext
    simp only [cut_f, objectTensor, mapFunctor,
      tensorHom_id, id_tensorHom, tensorUnit_X, Functor.LaxMonoidal.right_unitality]

end RMod.BrundanEllis.Stacking.KaroubiTensor
