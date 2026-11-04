import RMod.Hierarchy.Bridge.Grading
import RMod.Hierarchy.Instances.TotalFunctor
import RMod.Classification.Instances.Functors

/-!
# Recovering old superfunctors from enriched presentations

The total Hom equivalences conjugate an enriched functor into its old
linear form. This construction retains the object map and the grading.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
namespace RMod.Legacy.Hierarchy

theorem totalHomEquiv_symm_id (C : WeaklyPointedSuperfusion.{0, 0}) (X : C.data.Obj) :
    (totalHomEquiv C X X).symm (C.data.id X) = evenPoint ((ofOldSupercategoryData C).id X) :=
  (totalHomEquiv C X X).symm_apply_eq.mpr (totalHomEquiv_id C X).symm

theorem totalHomEquiv_symm_comp (C : WeaklyPointedSuperfusion.{0, 0})
    {X Y Z : C.data.Obj} (f : C.data.Hom X Y) (g : C.data.Hom Y Z) :
    (totalHomEquiv C X Z).symm (C.data.comp f g) =
      tComp (ofOldSupercategoryData C) ((totalHomEquiv C X Y).symm f) ((totalHomEquiv C Y Z).symm g) := by
  apply (totalHomEquiv C X Z).injective
  rw [LinearEquiv.apply_symm_apply, totalHomEquiv_comp,
    LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

variable {C D : WeaklyPointedSuperfusion.{0, 0}}
  (F : Superfunctor (ofOldSupercategory C) (ofOldSupercategory D))

def reflectSuperfunctorData : Classification.SuperfunctorData C.data D.data where
  obj := F.data.obj
  map {X Y} f := totalHomEquiv D _ _ (tMap F.data ((totalHomEquiv C X Y).symm f))

theorem reflectSuperfunctor_map {X Y : C.data.Obj} (f : THom (ofOldSupercategoryData C) X Y) :
    (reflectSuperfunctorData F).map (totalHomEquiv C X Y f) =
      totalHomEquiv D _ _ (tMap F.data f) := by
  change totalHomEquiv D _ _ (tMap F.data ((totalHomEquiv C X Y).symm (totalHomEquiv C X Y f))) = _
  rw [LinearEquiv.symm_apply_apply]

theorem reflectSuperfunctorLaws :
    Classification.SuperfunctorLaws C.data D.data (reflectSuperfunctorData F) where
  map_id X := by
    change totalHomEquiv D _ _ (tMap F.data ((totalHomEquiv C X X).symm (C.data.id X))) = _
    erw [totalHomEquiv_symm_id, tMap_id F, totalHomEquiv_id]
    rfl
  map_comp f g := by
    change totalHomEquiv D _ _ (tMap F.data ((totalHomEquiv C _ _).symm (C.data.comp f g))) = _
    erw [totalHomEquiv_symm_comp, tMap_comp F, totalHomEquiv_comp]
    rfl
  map_zero X Y := by
    change totalHomEquiv D _ _ (tMap F.data ((totalHomEquiv C X Y).symm 0)) = 0
    rw [map_zero, tMap_zero, map_zero]
  map_add {X Y} f g := by
    change totalHomEquiv D _ _ (tMap F.data ((totalHomEquiv C X Y).symm (C.data.add f g))) = _
    erw [(totalHomEquiv C X Y).symm.map_add, tMap_add F, (totalHomEquiv D _ _).map_add]
    rfl
  map_smul {X Y} r f := by
    change totalHomEquiv D _ _ (tMap F.data ((totalHomEquiv C X Y).symm (C.data.smul r f))) = _
    erw [(totalHomEquiv C X Y).symm.map_smul, tMap_smul F, (totalHomEquiv D _ _).map_smul]
    rfl
  map_grade {X Y a} f hf := by
    apply (totalHomEquiv_grade D _ _ _ a).mp
    apply tMap_mem_grade F
    apply (totalHomEquiv_grade C X Y _ a).mpr
    rw [LinearEquiv.apply_symm_apply]
    exact hf

def reflectSuperfunctor : Classification.Superfunctor C D :=
  ⟨reflectSuperfunctorData F, reflectSuperfunctorLaws F⟩

end RMod.Legacy.Hierarchy
