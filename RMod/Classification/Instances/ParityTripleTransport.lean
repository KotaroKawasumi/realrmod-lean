import RMod.Classification.Proofs.ParityTripleTransport

/-! # Completed transport to the common total parity -/

set_option autoImplicit false

namespace RMod.Classification

variable {A C : WeaklyPointedSuperfusion.{0, 0}}
  {S T R : SimpleObject A} {U V W : SimpleObject C} {p : Pi C.data} {a b : ZMod 2}
  {E : SpanSuperfunctor A C S.data.object U.data.object}
  {H : SpanSuperfunctor A C T.data.object V.data.object}
  {K : SpanSuperfunctor A C R.data.object W.data.object}
  {N : SpanSuperfunctor A C
    (simpleTensorRepresentative A (simpleTensorRepresentative A S T) R).data.object
    (simpleTensorRepresentative C (simpleTensorRepresentative C U V) W).data.object}

def parityTripleTransport (e : a = b) (η : ParityTripleComparison S T R U V W p E H K N a) :
    ParityTripleComparison S T R U V W p E H K N b where
  data := parityTripleTransportData e η.data
  laws := parityTripleTransportLaws e η

end RMod.Classification
