import RMod.Classification.Abstract.ParityTripleComparison
import RMod.Classification.Abstract.ParityTensorComparison
import RMod.Classification.Instances.TripleRightFunctor
import RMod.Classification.Instances.SpanMapIso

/-!
# Right triple tensorator followed by the specified right normalizer

Map the source associator, invert the outer and inner tensorators, then
apply R. Its common normal form uses the same bracketing as the left
route. The inverse retains the reversed list of all specified maps.
-/

set_option autoImplicit false

namespace RMod.Classification

variable {A C : WeaklyPointedSuperfusion.{0, 0}}
  (S T R : SimpleObject A) (U V W : SimpleObject C)
  {p : PiData C.data} {a b : ZMod 2}
  {E : SpanSuperfunctorData A C S.data.object U.data.object}
  {H : SpanSuperfunctorData A C T.data.object V.data.object}
  {K : SpanSuperfunctorData A C R.data.object W.data.object}
  {F : SpanSuperfunctorData A C (simpleTensorRepresentative A T R).data.object
    (simpleTensorRepresentative C V W).data.object}
  {N : SpanSuperfunctorData A C
    (simpleTensorRepresentative A S (simpleTensorRepresentative A T R)).data.object
    (simpleTensorRepresentative C U (simpleTensorRepresentative C V W)).data.object}

/-- The composite T_R from the right-bracketed twisted tensor product. -/
noncomputable def parityTripleRightTensorator
    (η : ParityTensorComparisonData T R V W p a H K F)
    (θ : ParityTensorComparisonData S (simpleTensorRepresentative A T R) U
      (simpleTensorRepresentative C V W) p b E F N)
    (X : HomogeneousSpanCategory A S.data.object) (Y : HomogeneousSpanCategory A T.data.object)
    (Z : HomogeneousSpanCategory A R.data.object) :
    IsoData C.data
      (C.data.tensorObj (C.data.tensorObj (E.obj X).obj
        (C.data.tensorObj (C.data.tensorObj (H.obj Y).obj (K.obj Z).obj) (p.factor a))) (p.factor b))
      (N.obj (rightTripleSpanObj A S T R X Y Z)).obj :=
  (((IsoData.refl C.data (E.obj X).obj).tensor C.data (η.app Y Z)).tensor C.data
    (IsoData.refl C.data (p.factor b))).trans C.data (θ.app X (spanTensorObj A T R Y Z))

noncomputable def parityTripleRightData
    (η : ParityTensorComparisonData T R V W p a H K F)
    (θ : ParityTensorComparisonData S (simpleTensorRepresentative A T R) U
      (simpleTensorRepresentative C V W) p b E F N) :
    ParityTripleComparisonData S T R U V W p (a + b) E H K (tripleRightFunctorData S T R U V W N) where
  app X Y Z :=
    (((SpanSuperfunctor.mapIsoData N
      (X := tripleSpanObjInRight A S T R X Y Z) (Y := rightTripleSpanObj A S T R X Y Z)
      (IsoData.assoc A.data X.obj Y.obj Z.obj)).trans C.data
        ((θ.app X (spanTensorObj A T R Y Z)).symm C.data)).trans C.data
          (((IsoData.refl C.data (E.obj X).obj).tensor C.data ((η.app Y Z).symm C.data)).tensor C.data
            (IsoData.refl C.data (p.factor b)))).trans C.data
              (p.normalRight (E.obj X).obj (H.obj Y).obj (K.obj Z).obj a b)

end RMod.Classification
