import RMod.Classification.Abstract.ParityTripleComparison
import RMod.Classification.Abstract.ParityTensorComparison

/-!
# Left triple tensorator followed by the specified left normalizer

Invert the outer and inner tensorators and then apply L. This retains
the exact even map from the transported left tensor product to the
common right-parity normal form, including the contraction sign.
-/

set_option autoImplicit false

namespace RMod.Classification

variable {A C : WeaklyPointedSuperfusion.{0, 0}}
  (S T R : SimpleObject A) (U V W : SimpleObject C)
  {p : PiData C.data} {a b : ZMod 2}
  {E : SpanSuperfunctorData A C S.data.object U.data.object}
  {H : SpanSuperfunctorData A C T.data.object V.data.object}
  {K : SpanSuperfunctorData A C R.data.object W.data.object}
  {F : SpanSuperfunctorData A C (simpleTensorRepresentative A S T).data.object
    (simpleTensorRepresentative C U V).data.object}
  {N : SpanSuperfunctorData A C
    (simpleTensorRepresentative A (simpleTensorRepresentative A S T) R).data.object
    (simpleTensorRepresentative C (simpleTensorRepresentative C U V) W).data.object}

/-- The composite T_L before applying the source associator. -/
noncomputable def parityTripleLeftTensorator
    (η : ParityTensorComparisonData S T U V p a E H F)
    (θ : ParityTensorComparisonData (simpleTensorRepresentative A S T) R
      (simpleTensorRepresentative C U V) W p b F K N)
    (X : HomogeneousSpanCategory A S.data.object) (Y : HomogeneousSpanCategory A T.data.object)
    (Z : HomogeneousSpanCategory A R.data.object) :
    IsoData C.data
      (C.data.tensorObj (C.data.tensorObj
        (C.data.tensorObj (C.data.tensorObj (E.obj X).obj (H.obj Y).obj) (p.factor a)) (K.obj Z).obj)
        (p.factor b)) (N.obj (tripleSpanObj A S T R X Y Z)).obj :=
  (((η.app X Y).tensor C.data (IsoData.refl C.data (K.obj Z).obj)).tensor C.data
    (IsoData.refl C.data (p.factor b))).trans C.data (θ.app (spanTensorObj A S T X Y) Z)

noncomputable def parityTripleLeftData
    (η : ParityTensorComparisonData S T U V p a E H F)
    (θ : ParityTensorComparisonData (simpleTensorRepresentative A S T) R
      (simpleTensorRepresentative C U V) W p b F K N) :
    ParityTripleComparisonData S T R U V W p (a + b) E H K N where
  app X Y Z := (((θ.app (spanTensorObj A S T X Y) Z).symm C.data).trans C.data
    ((((η.app X Y).symm C.data).tensor C.data (IsoData.refl C.data (K.obj Z).obj)).tensor C.data
      (IsoData.refl C.data (p.factor b)))).trans C.data
        (p.normalLeft (E.obj X).obj (H.obj Y).obj (K.obj Z).obj a b)

end RMod.Classification
