import RMod.Classification.Proofs.ParityTripleLeft

/-! # The completed left triple normalization -/

set_option autoImplicit false

namespace RMod.Classification

variable {A C : WeaklyPointedSuperfusion.{0, 0}}
  {S T R : SimpleObject A} {U V W : SimpleObject C} {p : Pi C.data} {a b : ZMod 2}
  {E : SpanSuperfunctor A C S.data.object U.data.object}
  {H : SpanSuperfunctor A C T.data.object V.data.object}
  {K : SpanSuperfunctor A C R.data.object W.data.object}
  {F : SpanSuperfunctor A C (simpleTensorRepresentative A S T).data.object
    (simpleTensorRepresentative C U V).data.object}
  {N : SpanSuperfunctor A C
    (simpleTensorRepresentative A (simpleTensorRepresentative A S T) R).data.object
    (simpleTensorRepresentative C (simpleTensorRepresentative C U V) W).data.object}

noncomputable def parityTripleLeft (η : ParityTensorComparison S T U V p E H F a)
    (θ : ParityTensorComparison (simpleTensorRepresentative A S T) R
      (simpleTensorRepresentative C U V) W p F K N b) :
    ParityTripleComparison S T R U V W p E H K N (a + b) where
  data := parityTripleLeftData S T R U V W η.data θ.data
  laws := parityTripleLeftLaws η θ

end RMod.Classification
