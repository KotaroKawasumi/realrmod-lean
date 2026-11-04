import RMod.Classification.Abstract.ParityTensorComparison
import RMod.Classification.Instances.RightFactorDeletion

/-! # From a homogeneous comparison to an even tensorator

First delete the right factor and then apply the inverse homogeneous
comparison. Both maps have degree a, so their composite has degree zero.
-/

set_option autoImplicit false

namespace RMod.Classification

variable {A C : WeaklyPointedSuperfusion.{0, 0}}
  {S T : SimpleObject A} {U V : SimpleObject C}
  {E : SpanSuperfunctorData A C S.data.object U.data.object}
  {H : SpanSuperfunctorData A C T.data.object V.data.object}
  {N : SpanSuperfunctorData A C (simpleTensorRepresentative A S T).data.object
    (simpleTensorRepresentative C U V).data.object}

def parityTensorComparisonData (p : PiData C.data) (a : ZMod 2)
    (η : TensorComparisonData S T U V E H N) :
    ParityTensorComparisonData S T U V p a E H N where
  app X Y := (p.rightFactorDeletion (C.data.tensorObj (E.obj X).obj (H.obj Y).obj) a).trans C.data
    ((η.app X Y).symm C.data)

end RMod.Classification
