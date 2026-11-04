import RMod.Classification.Proofs.ParityTensorComparison

/-! # The completed even multiplication comparison -/

set_option autoImplicit false

namespace RMod.Classification

variable {A C : WeaklyPointedSuperfusion.{0, 0}}
  {S T : SimpleObject A} {U V : SimpleObject C}
  {E : SpanSuperfunctor A C S.data.object U.data.object}
  {H : SpanSuperfunctor A C T.data.object V.data.object}
  {N : SpanSuperfunctor A C (simpleTensorRepresentative A S T).data.object
    (simpleTensorRepresentative C U V).data.object} {a : ZMod 2}

def parityTensorComparison (p : Pi C.data) (η : TensorComparison S T U V E H N a) :
    ParityTensorComparison S T U V p E H N a where
  data := parityTensorComparisonData p.data a η.data
  laws := parityTensorComparisonLaws p η

end RMod.Classification
