import RMod.Classification.Proofs.ParityTripleRight

/-! # The completed right triple normalization -/

set_option autoImplicit false

namespace RMod.Classification

variable {A C : WeaklyPointedSuperfusion.{0, 0}}
  {S T R : SimpleObject A} {U V W : SimpleObject C} {p : Pi C.data} {a b : ZMod 2}
  {E : SpanSuperfunctor A C S.data.object U.data.object}
  {H : SpanSuperfunctor A C T.data.object V.data.object}
  {K : SpanSuperfunctor A C R.data.object W.data.object}
  {F : SpanSuperfunctor A C (simpleTensorRepresentative A T R).data.object
    (simpleTensorRepresentative C V W).data.object}
  {N : SpanSuperfunctor A C
    (simpleTensorRepresentative A S (simpleTensorRepresentative A T R)).data.object
    (simpleTensorRepresentative C U (simpleTensorRepresentative C V W)).data.object}

noncomputable def parityTripleRight (η : ParityTensorComparison T R V W p H K F a)
    (θ : ParityTensorComparison S (simpleTensorRepresentative A T R) U
      (simpleTensorRepresentative C V W) p E F N b) :
    ParityTripleComparison S T R U V W p E H K (tripleRightFunctor S T R U V W N) (a + b) where
  data := parityTripleRightData S T R U V W η.data θ.data
  laws := parityTripleRightLaws η θ

end RMod.Classification
