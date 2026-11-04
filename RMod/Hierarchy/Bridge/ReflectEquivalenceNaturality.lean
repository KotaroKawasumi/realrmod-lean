import RMod.Hierarchy.Bridge.ReflectEquivalenceData
import RMod.Hierarchy.Bridge.ReflectTensor

/-!
# Naturality after evaluating the enriched equivalence

Conjugating total maps by the Hom equivalences preserves the unit, counit,
and convention-corrected tensor naturality on all morphisms.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open CategoryTheory
namespace RMod.Legacy.Hierarchy
variable {C D : WeaklyPointedSuperfusion.{0, 0}}
  (E : MonoidalSuperequivalence (ofOldMonoidalSupercategory C) (ofOldMonoidalSupercategory D))

theorem reflect_unit_natural {X Y : C.data.Obj} (f : C.data.Hom X Y) :
    C.data.comp f ((reflectEquivalenceData E).unitHom Y) =
      C.data.comp ((reflectEquivalenceData E).unitHom X)
        ((reflectEquivalenceData E).backward.map ((reflectEquivalenceData E).forward.map f)) := by
  have h := congrArg (totalHomEquiv C X _)
    (E.laws.unit_natural ((totalHomEquiv C X Y).symm f))
  erw [totalHomEquiv_comp, totalHomEquiv_comp, LinearEquiv.apply_symm_apply,
    ← oldValue_total, ← oldValue_total,
    ← reflectSuperfunctor_map E.backward, ← reflectSuperfunctor_map E.forward,
    LinearEquiv.apply_symm_apply] at h
  exact h

theorem reflect_counit_natural {X Y : D.data.Obj} (f : D.data.Hom X Y) :
    D.data.comp ((reflectEquivalenceData E).forward.map ((reflectEquivalenceData E).backward.map f))
      ((reflectEquivalenceData E).counitHom Y) =
      D.data.comp ((reflectEquivalenceData E).counitHom X) f := by
  have h := congrArg (totalHomEquiv D _ Y)
    (E.laws.counit_natural ((totalHomEquiv D X Y).symm f))
  erw [totalHomEquiv_comp, totalHomEquiv_comp, LinearEquiv.apply_symm_apply,
    ← oldValue_total, ← oldValue_total,
    ← reflectSuperfunctor_map E.forward, ← reflectSuperfunctor_map E.backward,
    LinearEquiv.apply_symm_apply] at h
  exact h

theorem reflect_tensor_natural {X X' Y Y' : C.data.Obj}
    (f : C.data.Hom X X') (g : C.data.Hom Y Y') :
    D.data.comp (D.data.tensorHom ((reflectMonoidalFunctorData E).map f) ((reflectMonoidalFunctorData E).map g))
      ((reflectMonoidalFunctorData E).tensorHom X' Y') =
    D.data.comp ((reflectMonoidalFunctorData E).tensorHom X Y)
      ((reflectMonoidalFunctorData E).map (C.data.tensorHom f g)) := by
  let f₀ := (totalHomEquiv C X X').symm f
  let g₀ := (totalHomEquiv C Y Y').symm g
  let L := legacyTensor (ofOldMonoidalSupercategory D)
    (tMap E.data.forward f₀) (tMap E.data.forward g₀)
  let R := tMap E.data.forward (legacyTensor (ofOldMonoidalSupercategory C) f₀ g₀)
  let μ := evenPoint (E.data.tensorIso X Y).hom
  let μ' := evenPoint (E.data.tensorIso X' Y').hom
  have h := congrArg (totalHomEquiv D
    (D.data.tensorObj (E.data.forward.obj X) (E.data.forward.obj Y))
    (E.data.forward.obj (C.data.tensorObj X' Y')))
    (legacyTensor_natural E ((totalHomEquiv C X X').symm f) ((totalHomEquiv C Y Y').symm g))
  erw [totalHomEquiv_comp D _ _ _ L μ', totalHomEquiv_comp D _ _ _ μ R,
    totalHomEquiv_legacyTensor D (tMap E.data.forward f₀) (tMap E.data.forward g₀),
    ← oldValue_total D (E.data.tensorIso X' Y').hom, ← oldValue_total D (E.data.tensorIso X Y).hom,
    ← reflectSuperfunctor_map E.forward (legacyTensor (ofOldMonoidalSupercategory C) f₀ g₀),
    totalHomEquiv_legacyTensor C f₀ g₀,
    LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h
  exact h

end RMod.Legacy.Hierarchy
