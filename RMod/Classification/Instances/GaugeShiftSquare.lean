import RMod.Classification.Instances.GaugeLocalNormalizers

/-!
# The specified even cancellation of two identical right shifts

Contract the pair in its existing order, use a+a=0, and apply the right
unitor. Reversing these exact steps supplies the inverse comparison.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification.PiData

def rightShiftSquare {C : WeaklyPointedSuperfusionData.{u, v}} (p : PiData C) (X : C.Obj) (a : ZMod 2) :
    IsoData C (C.tensorObj (C.tensorObj X (p.factor a)) (p.factor a)) X :=
  ((p.rightFactorPairNormalizer X a a).trans C
    (IsoData.ofEq C (congrArg (fun q => C.tensorObj X (p.factor q))
      (CharTwo.add_self_eq_zero a)))).trans C (IsoData.rightUnit C X)

end RMod.Classification.PiData
