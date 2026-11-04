import RMod.Classification.Proofs.TripleLeftComparison

/-! # The completed left-associated triple comparison -/

set_option autoImplicit false

namespace RMod.Classification

variable {A C : WeaklyPointedSuperfusion.{0, 0}}
  {S T R : SimpleObject A} {U V W : SimpleObject C}
  {E : SpanSuperfunctor A C S.data.object U.data.object}
  {H : SpanSuperfunctor A C T.data.object V.data.object}
  {K : SpanSuperfunctor A C R.data.object W.data.object}
  {F : SpanSuperfunctor A C (simpleTensorRepresentative A S T).data.object
    (simpleTensorRepresentative C U V).data.object}
  {N : SpanSuperfunctor A C
    (simpleTensorRepresentative A (simpleTensorRepresentative A S T) R).data.object
    (simpleTensorRepresentative C (simpleTensorRepresentative C U V) W).data.object} {a b : ZMod 2}

noncomputable def tripleLeftComparison (η : TensorComparison S T U V E H F a)
    (θ : TensorComparison (simpleTensorRepresentative A S T) R (simpleTensorRepresentative C U V) W F K N b) :
    TripleComparison S T R U V W E H K N (a + b) :=
  ⟨tripleLeftComparisonData S T R U V W η.data θ.data, tripleLeftComparisonLaws η θ⟩

end RMod.Classification
