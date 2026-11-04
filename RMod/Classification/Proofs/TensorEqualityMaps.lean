import RMod.Classification.Proofs.IsoCalculus

/-! # Tensoring the retained raw equality comparisons -/

set_option autoImplicit false
universe u v

namespace RMod.Classification

variable {C : WeaklyPointedSuperfusionData.{u, v}} (hC : WeaklyPointedSuperfusionLaws C)

include hC

theorem isoData_tensorRight_ofEq {X Y : C.Obj} (e : X = Y) (P : C.Obj) :
    C.tensorHom (IsoData.ofEq C e).hom (C.id P) =
      (IsoData.ofEq C (congrArg (fun T => C.tensorObj T P) e)).hom := by
  cases e
  exact hC.tensor_id X P

end RMod.Classification
