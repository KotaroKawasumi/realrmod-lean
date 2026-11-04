import RMod.Hierarchy.Bridge.ReflectEquivalenceNaturality
import RMod.Hierarchy.Bridge.ReflectEquivalenceCoherence

/-!
# Reflecting a monoidal superequivalence to the original presentation

The recovered linear functors and comparison maps satisfy every original
law. This allows the original gauge necessity theorem to be reused without
strengthening the new definition of equivalence.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RMod.Legacy.Hierarchy
variable {C D : WeaklyPointedSuperfusion.{0, 0}}
  (E : MonoidalSuperequivalence (ofOldMonoidalSupercategory C) (ofOldMonoidalSupercategory D))

theorem reflectMonoidalFunctorLaws :
    Classification.MonoidalSuperfunctorLaws C.data D.data (reflectMonoidalFunctorData E) where
  toSuperfunctorLaws := reflectSuperfunctorLaws E.forward
  tensor_hom_even X Y := oldValue_even D (E.data.tensorIso X Y).hom
  tensor_inv_even X Y := oldValue_even D (E.data.tensorIso X Y).inv
  tensor_hom_inv X Y := oldValue_hom_inv D (E.data.tensorIso X Y)
  tensor_inv_hom X Y := oldValue_inv_hom D (E.data.tensorIso X Y)
  unit_hom_even := oldValue_even D E.data.unitIso.hom
  unit_inv_even := oldValue_even D E.data.unitIso.inv
  unit_hom_inv := oldValue_hom_inv D E.data.unitIso
  unit_inv_hom := oldValue_inv_hom D E.data.unitIso
  tensor_naturality := reflect_tensor_natural E
  associativity := reflect_associativity E
  left_unit := reflect_left_unit E
  right_unit := reflect_right_unit E

theorem reflectEquivalenceLaws :
    Classification.MonoidalSuperequivalenceLaws C.data D.data (reflectEquivalenceData E) where
  forward := reflectMonoidalFunctorLaws E
  backward := reflectSuperfunctorLaws E.backward
  unit_hom_even X := oldValue_even C (E.data.unit X).hom
  unit_inv_even X := oldValue_even C (E.data.unit X).inv
  unit_hom_inv X := oldValue_hom_inv C (E.data.unit X)
  unit_inv_hom X := oldValue_inv_hom C (E.data.unit X)
  counit_hom_even X := oldValue_even D (E.data.counit X).hom
  counit_inv_even X := oldValue_even D (E.data.counit X).inv
  counit_hom_inv X := oldValue_hom_inv D (E.data.counit X)
  counit_inv_hom X := oldValue_inv_hom D (E.data.counit X)
  unit_naturality := reflect_unit_natural E
  counit_naturality := reflect_counit_natural E

def reflectEquivalence : Classification.MonoidalSuperequivalence C D :=
  ⟨reflectEquivalenceData E, reflectEquivalenceLaws E⟩

end RMod.Legacy.Hierarchy
