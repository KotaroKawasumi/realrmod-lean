import RMod.Classification.Abstract.ParityTripleComparison
import RMod.Classification.Instances.RightFactorDeletion

/-!
# Deleting the common parity factor from a triple normal form

The inverse associator converts the remaining right-bracketed ordinary
objects to the convention used by homogeneous triple comparisons.
-/

set_option autoImplicit false

namespace RMod.Classification

variable {A C : WeaklyPointedSuperfusion.{0, 0}}
  {S T R : SimpleObject A} {U V W : SimpleObject C}
  {E : SpanSuperfunctorData A C S.data.object U.data.object}
  {H : SpanSuperfunctorData A C T.data.object V.data.object}
  {K : SpanSuperfunctorData A C R.data.object W.data.object}
  {N : SpanSuperfunctorData A C
    (simpleTensorRepresentative A (simpleTensorRepresentative A S T) R).data.object
    (simpleTensorRepresentative C (simpleTensorRepresentative C U V) W).data.object}

def parityTripleReductionData (p : PiData C.data) (a : ZMod 2)
    (η : ParityTripleComparisonData S T R U V W p a E H K N) :
    TripleComparisonData S T R U V W E H K N where
  app X Y Z := ((η.app X Y Z).trans C.data
    (p.rightFactorDeletion (C.data.tensorObj (E.obj X).obj (C.data.tensorObj (H.obj Y).obj (K.obj Z).obj)) a)).trans C.data
    ((IsoData.assoc C.data (E.obj X).obj (H.obj Y).obj (K.obj Z).obj).symm C.data)

end RMod.Classification
