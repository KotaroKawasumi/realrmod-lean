import RMod.Hierarchy.Bridge.EnrichmentLaws
import RMod.Hierarchy.Instances.HomogeneousLine
import RMod.Hierarchy.Instances.EvenLinear
import RMod.Classification.Instances.LinearMonoidal

/-!
# The old and new even categories

Maps from the even real line correspond to the old degree-zero submodule.
The resulting functor keeps the objects and is a linear equivalence of
ordinary categories.
-/

noncomputable section
set_option autoImplicit false
open CategoryTheory
namespace RMod.Legacy.Hierarchy
variable (C : WeaklyPointedSuperfusion.{0, 0})

abbrev OldEven := Superfusion.Category.EvenSubcategory ℝ (Classification.LinearCategory C)
def oldEvenObj (X : C.data.Obj) : OldEven C := ⟨X⟩

def oldEvenHomEquiv (X Y : C.data.Obj) : Classification.LinearCategory.grade C X Y 0 ≃ₗ[ℝ]
    (oldEvenObj C X ⟶ oldEvenObj C Y) where
  toFun f := ⟨f.val, f.property⟩
  invFun f := ⟨f.hom, f.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def evenHomEquiv (X Y : C.data.Obj) :
    (evenObj (ofOldSupercategory C) X ⟶ evenObj (ofOldSupercategory C) Y) ≃ₗ[ℝ]
      (oldEvenObj C X ⟶ oldEvenObj C Y) :=
  (homogeneousHomEquiv (oldEnrichedHom C X Y) 0).trans (oldEvenHomEquiv C X Y)

@[simp]
theorem evenHomEquiv_apply (X Y : C.data.Obj) (f : EHom (ofOldSupercategoryData C) X Y) :
    (evenHomEquiv C X Y f).hom = (evenPoint f 0).val := rfl

theorem evenHomEquiv_id (X : C.data.Obj) :
    evenHomEquiv C X X ((ofOldSupercategoryData C).id X) = 𝟙 (oldEvenObj C X) := by
  apply WideSubcategory.hom_ext
  exact oldEnrichedId_zero C X

theorem evenHomEquiv_comp (X Y Z : C.data.Obj)
    (f : EHom (ofOldSupercategoryData C) X Y) (g : EHom (ofOldSupercategoryData C) Y Z) :
    evenHomEquiv C X Z (eComp (ofOldSupercategoryData C) f g) =
      evenHomEquiv C X Y f ≫ evenHomEquiv C Y Z g := by
  apply WideSubcategory.hom_ext
  change (evenPoint (eComp (ofOldSupercategoryData C) f g) 0).val = _
  rw [evenPoint_comp, tComp_even_left]
  exact oldEnrichedComp_tmul C X Y Z 0 0 0 rfl _ _

def evenForget : Even (ofOldSupercategory C) ⥤ OldEven C where
  obj X := oldEvenObj C X
  map {X Y} f := evenHomEquiv C X Y f
  map_id X := evenHomEquiv_id C X
  map_comp f g := evenHomEquiv_comp C _ _ _ f g

instance evenForget_faithful : (evenForget C).Faithful where
  map_injective {X Y} {_ _} h := (evenHomEquiv C X Y).injective h
instance evenForget_full : (evenForget C).Full where
  map_surjective := (evenHomEquiv C _ _).surjective
instance evenForget_essSurj : (evenForget C).EssSurj where
  mem_essImage Y := ⟨evenObj (ofOldSupercategory C) Y.obj, ⟨Iso.refl Y⟩⟩
instance evenForget_isEquivalence : (evenForget C).IsEquivalence where
instance evenForget_additive : (evenForget C).Additive where
  map_add {X Y} {f g} := (evenHomEquiv C X Y).map_add f g
instance evenForget_linear : (evenForget C).Linear ℝ where
  map_smul {X Y} f r := (evenHomEquiv C X Y).map_smul r f

def evenEquivalence : Even (ofOldSupercategory C) ≌ OldEven C :=
  (evenForget C).asEquivalence

end RMod.Legacy.Hierarchy
