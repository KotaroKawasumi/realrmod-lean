import RMod.Hierarchy.Bridge.ReflectSuperfunctors
import RMod.Hierarchy.Bridge.OldEvenValues
import RMod.Hierarchy.Instances.EquivalenceFunctors

/-!
# Data of reflected monoidal superequivalences

Evaluation in the old Hom spaces retains every specified comparison map
and its inverse. The even adapter supplies their grading and inverse laws.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.MonoidalCategory
namespace RMod.Legacy.Hierarchy

theorem oldValue_total (C : WeaklyPointedSuperfusion.{0, 0})
    {X Y : Even (ofOldSupercategory C)} (f : X ⟶ Y) :
    oldValue C f = totalHomEquiv C X Y (evenPoint f) := (totalHomEquiv_even C X Y f).symm

theorem oldValue_even (C : WeaklyPointedSuperfusion.{0, 0})
    {X Y : Even (ofOldSupercategory C)} (f : X ⟶ Y) :
    C.data.IsHomogeneous 0 (oldValue C f) := (evenHomEquiv C X Y f).property

theorem oldValue_hom_inv (C : WeaklyPointedSuperfusion.{0, 0})
    {X Y : Even (ofOldSupercategory C)} (e : X ≅ Y) :
    C.data.comp (oldValue C e.hom) (oldValue C e.inv) = C.data.id X := by
  rw [← oldValue_comp, e.hom_inv_id, oldValue_id]

theorem oldValue_inv_hom (C : WeaklyPointedSuperfusion.{0, 0})
    {X Y : Even (ofOldSupercategory C)} (e : X ≅ Y) :
    C.data.comp (oldValue C e.inv) (oldValue C e.hom) = C.data.id Y := by
  rw [← oldValue_comp, e.inv_hom_id, oldValue_id]

theorem reflectSuperfunctor_even {C D : WeaklyPointedSuperfusion.{0, 0}}
    (F : Superfunctor (ofOldSupercategory C) (ofOldSupercategory D))
    {X Y : Even (ofOldSupercategory C)} (f : X ⟶ Y) :
    (reflectSuperfunctorData F).map (oldValue C f) =
      oldValue D (F.enriched.forget.map f) := by
  rw [oldValue_total, reflectSuperfunctor_map, oldValue_total]
  exact congrArg (totalHomEquiv D _ _) (tMap_evenPoint F f)

variable {C D : WeaklyPointedSuperfusion.{0, 0}}
  (E : MonoidalSuperequivalence (ofOldMonoidalSupercategory C) (ofOldMonoidalSupercategory D))

def reflectMonoidalFunctorData : Classification.MonoidalSuperfunctorData C.data D.data where
  toPrefunctor := reflectSuperfunctorData E.forward
  tensorHom X Y := oldValue D (E.data.tensorIso X Y).hom
  tensorInv X Y := oldValue D (E.data.tensorIso X Y).inv
  unitHom := oldValue D E.data.unitIso.hom
  unitInv := oldValue D E.data.unitIso.inv

def reflectEquivalenceData : Classification.MonoidalSuperequivalenceData C.data D.data where
  forward := reflectMonoidalFunctorData E
  backward := reflectSuperfunctorData E.backward
  unitHom X := oldValue C (E.data.unit X).hom
  unitInv X := oldValue C (E.data.unit X).inv
  counitHom X := oldValue D (E.data.counit X).hom
  counitInv X := oldValue D (E.data.counit X).inv

end RMod.Legacy.Hierarchy
