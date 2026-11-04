import RMod.Hierarchy.Bridge.ToOld
import RMod.Hierarchy.Bridge.EvenCategory
import RMod.Hierarchy.Bridge.TotalCategory

/-!
# Underlying category equivalences for the extracted presentation

The total category retains exactly the same morphisms. In the even
category, evaluation identifies maps from the even line with the old
homogeneous subtype. These linear equivalences retain all objects.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
namespace RMod.Legacy.Hierarchy
variable (A : WeaklyPointedFusionPiSupercategory)

abbrev legacyCategory := (toOldPiSuperfusion A).toWeaklyPointedSuperfusion

def legacyTotalHomEquiv (X Y : A.data.Obj) :
    THom A.data.toSupercategoryData X Y ≃ₗ[ℝ]
      (@Quiver.Hom (Classification.LinearCategory (legacyCategory A)) inferInstance X Y) where
  toFun f := f
  invFun f := f
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def legacyTotalEndEquiv (X : A.data.Obj) :
    End (totalObj A.toMonoidalPiSupercategory.monoidal.super X) ≃ₐ[ℝ]
      @End (Classification.LinearCategory (legacyCategory A)) inferInstance X :=
  AlgEquiv.ofLinearEquiv (legacyTotalHomEquiv A X X) rfl (fun _ _ => rfl)

def legacyEvenHomEquiv (X Y : A.data.Obj) :
    EHom A.data.toSupercategoryData X Y ≃ₗ[ℝ]
      (oldEvenObj (legacyCategory A) X ⟶ oldEvenObj (legacyCategory A) Y) where
  toFun f := ⟨evenPoint f, evenPoint_mem_grade A.toMonoidalPiSupercategory.monoidal.super f⟩
  invFun f := (evenHomGradeEquiv A.toMonoidalPiSupercategory.monoidal.super X Y).symm ⟨f.hom, f.property⟩
  left_inv f := (evenHomGradeEquiv A.toMonoidalPiSupercategory.monoidal.super X Y).left_inv f
  right_inv f := by
    apply WideSubcategory.hom_ext
    exact congrArg Subtype.val
      ((evenHomGradeEquiv A.toMonoidalPiSupercategory.monoidal.super X Y).apply_symm_apply ⟨f.hom, f.property⟩)
  map_add' f g := by
    apply WideSubcategory.hom_ext
    exact congrArg Subtype.val
      ((evenHomGradeEquiv A.toMonoidalPiSupercategory.monoidal.super X Y).map_add f g)
  map_smul' r f := by
    apply WideSubcategory.hom_ext
    exact congrArg Subtype.val
      ((evenHomGradeEquiv A.toMonoidalPiSupercategory.monoidal.super X Y).map_smul r f)

def legacyEvenForget : Even A.toMonoidalPiSupercategory.monoidal.super ⥤ OldEven (legacyCategory A) where
  obj X := oldEvenObj (legacyCategory A) X
  map {X Y} f := legacyEvenHomEquiv A X Y f
  map_id _ := rfl
  map_comp f g := by
    apply WideSubcategory.hom_ext
    exact evenPoint_comp A.data.toSupercategoryData f g

instance : (legacyEvenForget A).Faithful where
  map_injective {X Y} {_ _} h := (legacyEvenHomEquiv A X Y).injective h
instance : (legacyEvenForget A).Full where
  map_surjective := (legacyEvenHomEquiv A _ _).surjective
instance : (legacyEvenForget A).EssSurj where
  mem_essImage Y := ⟨evenObj _ Y.obj, ⟨Iso.refl Y⟩⟩
instance : (legacyEvenForget A).IsEquivalence where
instance : (legacyEvenForget A).Additive where
  map_add {X Y} {f g} := (legacyEvenHomEquiv A X Y).map_add f g
instance : (legacyEvenForget A).Linear ℝ where
  map_smul {X Y} f r := (legacyEvenHomEquiv A X Y).map_smul r f

end RMod.Legacy.Hierarchy
