import RMod.Classification.Proofs.TensorCalculus

/-!
# Composition under the two parity-positioned tensor whiskerings

Whiskering a composite by identities introduces no super interchange
sign. These two formulas retain the position of the outer right parity
factor and apply to arbitrary maps in the varying tensor factor.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification

variable {C : WeaklyPointedSuperfusionData.{u, v}}
  (hC : WeaklyPointedSuperfusionLaws C)
  {X Y Z : C.Obj} (f : C.Hom X Y) (g : C.Hom Y Z) (T P : C.Obj)

include hC

theorem tensor_right_right_comp :
    C.tensorHom (C.tensorHom (C.comp f g) (C.id T)) (C.id P) =
    C.comp (C.tensorHom (C.tensorHom f (C.id T)) (C.id P))
      (C.tensorHom (C.tensorHom g (C.id T)) (C.id P)) := by
  rw [interchange_second_even hC _ _ _ _ (hC.id_even P), hC.comp_id,
    interchange_second_even hC _ _ _ _ (hC.id_even T), hC.comp_id]

theorem tensor_left_right_comp :
    C.tensorHom (C.tensorHom (C.id T) (C.comp f g)) (C.id P) =
    C.comp (C.tensorHom (C.tensorHom (C.id T) f) (C.id P))
      (C.tensorHom (C.tensorHom (C.id T) g) (C.id P)) := by
  rw [interchange_second_even hC _ _ _ _ (hC.id_even P), hC.comp_id,
    interchange_first_even hC _ _ _ _ (hC.id_even T), hC.comp_id]

end RMod.Classification
