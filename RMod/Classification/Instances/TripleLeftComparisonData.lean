import RMod.Classification.Abstract.TripleComparison
import RMod.Classification.Abstract.TensorComparison

/-!
# The left-associated triple comparison data

Apply the outer binary comparison to the product of the first two inputs
and the third input. Then tensor the inner comparison with the identity
of the third image. The specified inverse is the reversed composite of
the two specified inverses.
-/

set_option autoImplicit false

namespace RMod.Classification

variable {A C : WeaklyPointedSuperfusion.{0, 0}}
  (S T R : SimpleObject A) (U V W : SimpleObject C)
  {E : SpanSuperfunctorData A C S.data.object U.data.object}
  {H : SpanSuperfunctorData A C T.data.object V.data.object}
  {K : SpanSuperfunctorData A C R.data.object W.data.object}
  {F : SpanSuperfunctorData A C (simpleTensorRepresentative A S T).data.object
    (simpleTensorRepresentative C U V).data.object}
  {N : SpanSuperfunctorData A C
    (simpleTensorRepresentative A (simpleTensorRepresentative A S T) R).data.object
    (simpleTensorRepresentative C (simpleTensorRepresentative C U V) W).data.object}

noncomputable def tripleLeftComparisonData
    (η : TensorComparisonData S T U V E H F)
    (θ : TensorComparisonData (simpleTensorRepresentative A S T) R
      (simpleTensorRepresentative C U V) W F K N) : TripleComparisonData S T R U V W E H K N where
  app X Y Z := (θ.app (spanTensorObj A S T X Y) Z).trans C.data
    ((η.app X Y).tensor C.data (IsoData.refl C.data (K.obj Z).obj))

end RMod.Classification
