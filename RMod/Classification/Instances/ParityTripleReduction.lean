import RMod.Classification.Proofs.ParityTripleReduction

/-! # The completed homogeneous reduction of an even triple comparison -/

set_option autoImplicit false

namespace RMod.Classification

variable {A C : WeaklyPointedSuperfusion.{0, 0}}
  {S T R : SimpleObject A} {U V W : SimpleObject C} {p : Pi C.data}
  {E : SpanSuperfunctor A C S.data.object U.data.object}
  {H : SpanSuperfunctor A C T.data.object V.data.object}
  {K : SpanSuperfunctor A C R.data.object W.data.object}
  {N : SpanSuperfunctor A C
    (simpleTensorRepresentative A (simpleTensorRepresentative A S T) R).data.object
    (simpleTensorRepresentative C (simpleTensorRepresentative C U V) W).data.object} {a : ZMod 2}

def parityTripleReduction (η : ParityTripleComparison S T R U V W p E H K N a) :
    TripleComparison S T R U V W E H K N a where
  data := parityTripleReductionData p.data a η.data
  laws := parityTripleReductionLaws η

end RMod.Classification
