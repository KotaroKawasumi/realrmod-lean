import RMod.Classification.Abstract.ParityTripleComparison

/-!
# Identifying equal total parities in the normal form

The equality from the two-cocycle equation is realized by the identity
isomorphism between the equal parity-factor objects. No comparison
scalar is chosen or inserted at this step.
-/

set_option autoImplicit false

namespace RMod.Classification

variable {A C : WeaklyPointedSuperfusion.{0, 0}}
  {S T R : SimpleObject A} {U V W : SimpleObject C} {p : PiData C.data} {a b : ZMod 2}
  {E : SpanSuperfunctorData A C S.data.object U.data.object}
  {H : SpanSuperfunctorData A C T.data.object V.data.object}
  {K : SpanSuperfunctorData A C R.data.object W.data.object}
  {N : SpanSuperfunctorData A C
    (simpleTensorRepresentative A (simpleTensorRepresentative A S T) R).data.object
    (simpleTensorRepresentative C (simpleTensorRepresentative C U V) W).data.object}

def parityTripleTransportData (e : a = b)
    (η : ParityTripleComparisonData S T R U V W p a E H K N) :
    ParityTripleComparisonData S T R U V W p b E H K N where
  app X Y Z := (η.app X Y Z).trans C.data
    (IsoData.ofEq C.data (congrArg (fun q => C.data.tensorObj
      (C.data.tensorObj (E.obj X).obj (C.data.tensorObj (H.obj Y).obj (K.obj Z).obj)) (p.factor q)) e))

end RMod.Classification
