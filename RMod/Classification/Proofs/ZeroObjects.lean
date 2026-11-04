import RMod.Classification.Proofs.TensorCalculus

/-!
# Zero objects and retracts in the raw category interface

An identity equal to zero forces all incoming and outgoing maps to vanish.
It is inherited by retracts and by tensoring on either side. These short
consequences of the existing laws avoid adding a separate zero-object
structure to the statement.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification

variable {C : WeaklyPointedSuperfusionData.{u, v}}
  (hC : WeaklyPointedSuperfusionLaws C)

include hC

theorem hom_eq_zero_of_source {X Y : C.Obj} (hX : C.id X = C.zero) (f : C.Hom X Y) :
    f = C.zero := by
  rw [← hC.id_comp f, hX, raw_zero_comp hC]

theorem hom_eq_zero_of_target {X Y : C.Obj} (hY : C.id Y = C.zero) (f : C.Hom X Y) :
    f = C.zero := by
  rw [← hC.comp_id f, hY, raw_comp_zero hC]

theorem id_zero_of_retract {X Y : C.Obj} (i : C.Hom X Y) (p : C.Hom Y X)
    (hip : C.comp i p = C.id X) (hY : C.id Y = C.zero) : C.id X = C.zero := by
  rw [← hip, hom_eq_zero_of_target hC hY i, raw_zero_comp hC]

theorem tensor_id_zero_left {X : C.Obj} (hX : C.id X = C.zero) (Y : C.Obj) :
    C.id (C.tensorObj X Y) = C.zero := by
  rw [← hC.tensor_id, hX, tensor_zero_left hC]

theorem tensor_id_zero_right (X : C.Obj) {Y : C.Obj} (hY : C.id Y = C.zero) :
    C.id (C.tensorObj X Y) = C.zero := by
  rw [← hC.tensor_id, hY, tensor_zero_right hC]

end RMod.Classification
