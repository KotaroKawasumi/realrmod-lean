import RMod.Classification.Instances.SimpleOrbitMultiplication

/-!
# The tensor unit is the identity of the simple-orbit product

The inverse unitors are nonzero even maps from a simple into its tensor
product with the unit. The constituent-detection theorem identifies the
selected product class directly from these structural maps.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : WeaklyPointedSuperfusion.{0, 0})

theorem simpleOrbitMul_unit (x : SimpleOrbit C) : simpleOrbitMul C x (unitOrbit C) = x := by
  refine Quotient.inductionOn x ?_
  intro X
  apply Quotient.sound
  apply SameParityOrbit.symm
  apply simple_orbit_of_map_to_tensor C X (unitSimple C) X.laws.simple
    (C.data.rightUnitorInv X.data.object) (C.laws.right_unitor_inv_even _)
  intro hz
  change C.data.rightUnitorInv X.data.object =
    (C.data.zero : C.data.Hom X.data.object (C.data.tensorObj X.data.object C.data.tensorUnit)) at hz
  have h := C.laws.right_unitor_inv_hom X.data.object
  rw [hz, raw_zero_comp C.laws] at h
  exact simple_id_ne_zero C.laws X.laws.simple h.symm

theorem unit_simpleOrbitMul (x : SimpleOrbit C) : simpleOrbitMul C (unitOrbit C) x = x := by
  refine Quotient.inductionOn x ?_
  intro X
  apply Quotient.sound
  apply SameParityOrbit.symm
  apply simple_orbit_of_map_to_tensor C (unitSimple C) X X.laws.simple
    (C.data.leftUnitorInv X.data.object) (C.laws.left_unitor_inv_even _)
  intro hz
  change C.data.leftUnitorInv X.data.object =
    (C.data.zero : C.data.Hom X.data.object (C.data.tensorObj C.data.tensorUnit X.data.object)) at hz
  have h := C.laws.left_unitor_inv_hom X.data.object
  rw [hz, raw_zero_comp C.laws] at h
  exact simple_id_ne_zero C.laws X.laws.simple h.symm

end RMod.Classification
