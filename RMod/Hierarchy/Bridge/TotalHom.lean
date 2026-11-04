import RMod.Hierarchy.Bridge.EnrichmentLaws
import RMod.Hierarchy.Instances.TotalCategory

/-!
# Recovering the old total morphisms

The complementary old grading submodules identify pairs of homogeneous
components with the original Hom space. This linear equivalence preserves
identities and composition, so the enriched presentation retains the old
category operations.
-/

noncomputable section
set_option autoImplicit false
open CategoryTheory
namespace RMod.Legacy.Hierarchy
variable (C : WeaklyPointedSuperfusion.{0, 0})

def totalHomEquiv (X Y : Classification.LinearCategory C) :
    THom (ofOldSupercategoryData C) X Y ≃ₗ[ℝ] (X ⟶ Y) :=
  (LinearEquiv.piFinTwo ℝ (fun a => Classification.LinearCategory.grade C X Y a)).trans
    (Submodule.prodEquivOfIsCompl _ _ (Classification.LinearCategory.grade_isCompl C X Y))

@[simp]
theorem totalHomEquiv_apply (X Y : Classification.LinearCategory C)
    (f : THom (ofOldSupercategoryData C) X Y) :
    totalHomEquiv C X Y f = C.data.add (f 0).val (f 1).val := rfl

theorem totalHomEquiv_id (X : Classification.LinearCategory C) :
    totalHomEquiv C X X (evenPoint ((ofOldSupercategoryData C).id X)) = C.data.id X := by
  rw [totalHomEquiv_apply]
  have hzero : (evenPoint ((ofOldSupercategoryData C).id X) 0).val = C.data.id X :=
    oldEnrichedId_zero C X
  have hone : (evenPoint ((ofOldSupercategoryData C).id X) 1).val = C.data.zero := by
    simp [evenPoint, homogeneousPoint]
    rfl
  rw [hzero, hone, C.laws.add_zero]

theorem componentComp_ofOld (X Y Z : C.data.Obj) (i j a : ZMod 2) (h : i + j = a)
    (f : Classification.LinearCategory.grade C X Y i)
    (g : Classification.LinearCategory.grade C Y Z j) :
    (componentComp (ofOldSupercategoryData C) i j a h f g).val =
      C.data.comp f.val g.val := oldEnrichedComp_tmul C X Y Z i j a h f g

theorem totalHomEquiv_comp (X Y Z : Classification.LinearCategory C)
    (f : THom (ofOldSupercategoryData C) X Y) (g : THom (ofOldSupercategoryData C) Y Z) :
    totalHomEquiv C X Z (tComp (ofOldSupercategoryData C) f g) =
      C.data.comp (totalHomEquiv C X Y f) (totalHomEquiv C Y Z g) := by
  simp only [totalHomEquiv_apply, tComp_zero, tComp_one]
  change C.data.add
    (C.data.add (componentComp (ofOldSupercategoryData C) 0 0 0 rfl (f 0) (g 0)).val
      (componentComp (ofOldSupercategoryData C) 1 1 0 rfl (f 1) (g 1)).val)
    (C.data.add (componentComp (ofOldSupercategoryData C) 0 1 1 rfl (f 0) (g 1)).val
      (componentComp (ofOldSupercategoryData C) 1 0 1 rfl (f 1) (g 0)).val) = _
  rw [componentComp_ofOld, componentComp_ofOld, componentComp_ofOld, componentComp_ofOld,
    C.laws.add_comp, C.laws.comp_add, C.laws.comp_add]
  change ((f 0).val ≫ (g 0).val) + ((f 1).val ≫ (g 1).val) +
    (((f 0).val ≫ (g 1).val) + ((f 1).val ≫ (g 0).val)) =
      (((f 0).val ≫ (g 0).val) + ((f 0).val ≫ (g 1).val)) +
        (((f 1).val ≫ (g 0).val) + ((f 1).val ≫ (g 1).val))
  ac_rfl

end RMod.Legacy.Hierarchy
