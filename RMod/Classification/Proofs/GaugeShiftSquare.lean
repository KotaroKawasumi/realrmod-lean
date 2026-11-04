import RMod.Classification.Instances.GaugeShiftSquare
import RMod.Classification.Proofs.GaugeLocalNaturality

/-! # The even shift-square cancellation is natural on all morphisms -/

set_option autoImplicit false
universe u v

namespace RMod.Classification.PiLaws

variable {C : WeaklyPointedSuperfusionData.{u, v}}
  (hC : WeaklyPointedSuperfusionLaws C) {p : PiData C} (hp : PiLaws C p)

include hC hp

theorem rightShiftSquare_evenIso (X : C.Obj) (a : ZMod 2) :
    EvenIsoLaws C (p.rightShiftSquare X a) :=
  ((hp.rightFactorPairNormalizer_evenIso hC X a a).trans hC
    (EvenIsoLaws.ofEq hC (congrArg (fun q => C.tensorObj X (p.factor q))
      (CharTwo.add_self_eq_zero a)))).trans hC (EvenIsoLaws.rightUnit hC X)

theorem rightShiftSquare_naturality {X Y : C.Obj} (f : C.Hom X Y) (a : ZMod 2) :
    C.comp (C.tensorHom (C.tensorHom f (C.id (p.factor a))) (C.id (p.factor a)))
      (p.rightShiftSquare Y a).hom = C.comp (p.rightShiftSquare X a).hom f :=
  iso_naturality_trans hC
    (iso_naturality_trans hC (hp.rightFactorPairNormalizer_naturality hC f a a)
      (iso_naturality_tensor_ofEq hC (congrArg p.factor (CharTwo.add_self_eq_zero a)) f))
    (hC.right_unitor_naturality f)

end RMod.Classification.PiLaws
