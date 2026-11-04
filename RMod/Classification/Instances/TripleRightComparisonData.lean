import RMod.Classification.Abstract.TripleComparison
import RMod.Classification.Abstract.TensorComparison
import RMod.Classification.Instances.TripleRightFunctor
import RMod.Classification.Instances.SpanMapIso

/-!
# The right-associated triple route with specified associators

Map the source associator, apply the outer and then inner binary
comparisons, and invert the target associator. This gives a map between
the same left-bracketed input and output objects as the left route.
The inverse is the explicit reversed list of inverse maps.
-/

set_option autoImplicit false

namespace RMod.Classification

variable {A C : WeaklyPointedSuperfusion.{0, 0}}
  (S T R : SimpleObject A) (U V W : SimpleObject C)
  {E : SpanSuperfunctorData A C S.data.object U.data.object}
  {H : SpanSuperfunctorData A C T.data.object V.data.object}
  {K : SpanSuperfunctorData A C R.data.object W.data.object}
  {F : SpanSuperfunctorData A C (simpleTensorRepresentative A T R).data.object
    (simpleTensorRepresentative C V W).data.object}
  {N : SpanSuperfunctorData A C
    (simpleTensorRepresentative A S (simpleTensorRepresentative A T R)).data.object
    (simpleTensorRepresentative C U (simpleTensorRepresentative C V W)).data.object}

noncomputable def tripleRightComparisonData
    (η : TensorComparisonData T R V W H K F)
    (θ : TensorComparisonData S (simpleTensorRepresentative A T R) U
      (simpleTensorRepresentative C V W) E F N) :
    TripleComparisonData S T R U V W E H K (tripleRightFunctorData S T R U V W N) where
  app X Y Z :=
    (((SpanSuperfunctor.mapIsoData N
      (X := tripleSpanObjInRight A S T R X Y Z) (Y := rightTripleSpanObj A S T R X Y Z)
      (IsoData.assoc A.data X.obj Y.obj Z.obj)).trans C.data
        (θ.app X (spanTensorObj A T R Y Z))).trans C.data
          ((IsoData.refl C.data (E.obj X).obj).tensor C.data (η.app Y Z))).trans C.data
            ((IsoData.assoc C.data (E.obj X).obj (H.obj Y).obj (K.obj Z).obj).symm C.data)

end RMod.Classification
