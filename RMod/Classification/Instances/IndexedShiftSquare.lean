import RMod.Classification.Instances.GaugeShiftSquare

/-!
# Shift-square cancellation with an explicitly identified coordinate

The first comparison cancels two factors at the selected coordinate and
then identifies the ordinary object. The second first identifies the
inner shifted object, so its outer factor already has the final parity.
These are the two shapes occurring in the reindexed inverse functors.
-/

set_option autoImplicit false
universe u v w

namespace RMod.Classification.PiData

variable {C : WeaklyPointedSuperfusionData.{u, v}} (p : PiData C)
  {I : Type w} (X : I → C.Obj) (lam : I → ZMod 2) {i j : I} (e : j = i)

def indexedShiftSquare :
    IsoData C (C.tensorObj (C.tensorObj (X j) (p.factor (lam j))) (p.factor (lam j))) (X i) :=
  (p.rightShiftSquare (X j) (lam j)).trans C (IsoData.ofEq C (congrArg X e))

def indexedMixedShiftSquare :
    IsoData C (C.tensorObj (C.tensorObj (X j) (p.factor (lam j))) (p.factor (lam i))) (X i) :=
  (IsoData.ofEq C (congrArg (fun k => C.tensorObj (C.tensorObj (X k) (p.factor (lam k)))
    (p.factor (lam i))) e)).trans C (p.rightShiftSquare (X i) (lam i))

end RMod.Classification.PiData
