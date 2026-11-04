import Mathlib.CategoryTheory.Equivalence

/-!
# Components of a composite equivalence

These ordinary categorical identities remove the associativity and unit
constraints on functor composition before applying the grading laws of
the ambient supercategory.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

variable {C D K : Type*} [Category C] [Category D] [Category K]
  (F : C ≌ D) (G : D ≌ K)

theorem equivalence_trans_unit_hom (X : C) :
    (F.trans G).unitIso.hom.app X =
      F.unitIso.hom.app X ≫ F.inverse.map (G.unitIso.hom.app (F.functor.obj X)) := by
  change F.unitIso.hom.app X ≫
    (F.inverse.map ((𝟙 _) ≫ G.unitIso.hom.app (F.functor.obj X) ≫ 𝟙 _) ≫ 𝟙 _) = _
  rw [Category.id_comp, Category.comp_id, Category.comp_id]

theorem equivalence_trans_unit_inv (X : C) :
    (F.trans G).unitIso.inv.app X =
      F.inverse.map (G.unitIso.inv.app (F.functor.obj X)) ≫ F.unitIso.inv.app X := by
  change (𝟙 _ ≫ F.inverse.map ((𝟙 _ ≫ G.unitIso.inv.app (F.functor.obj X)) ≫ 𝟙 _)) ≫
    F.unitIso.inv.app X = _
  rw [Category.id_comp, Category.comp_id, Category.id_comp]

theorem equivalence_trans_counit_hom (Y : K) :
    (F.trans G).counitIso.hom.app Y =
      G.functor.map (F.counitIso.hom.app (G.inverse.obj Y)) ≫ G.counitIso.hom.app Y := by
  change 𝟙 _ ≫ G.functor.map (𝟙 _ ≫ F.counitIso.hom.app (G.inverse.obj Y) ≫ 𝟙 _) ≫
    G.counitIso.hom.app Y = _
  rw [Category.id_comp, Category.id_comp, Category.comp_id]

theorem equivalence_trans_counit_inv (Y : K) :
    (F.trans G).counitIso.inv.app Y =
      G.counitIso.inv.app Y ≫ G.functor.map (F.counitIso.inv.app (G.inverse.obj Y)) := by
  change (G.counitIso.inv.app Y ≫
    G.functor.map ((𝟙 _ ≫ F.counitIso.inv.app (G.inverse.obj Y)) ≫ 𝟙 _)) ≫ 𝟙 _ = _
  rw [Category.id_comp, Category.comp_id, Category.comp_id]

end RMod.Classification
