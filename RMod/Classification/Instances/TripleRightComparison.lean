import RMod.Classification.Proofs.TripleRightComparison

/-! # The completed right-associated triple comparison -/

set_option autoImplicit false

namespace RMod.Classification

variable {A C : WeaklyPointedSuperfusion.{0, 0}}
  {S T R : SimpleObject A} {U V W : SimpleObject C}
  {E : SpanSuperfunctor A C S.data.object U.data.object}
  {H : SpanSuperfunctor A C T.data.object V.data.object}
  {K : SpanSuperfunctor A C R.data.object W.data.object}
  {F : SpanSuperfunctor A C (simpleTensorRepresentative A T R).data.object
    (simpleTensorRepresentative C V W).data.object}
  {N : SpanSuperfunctor A C
    (simpleTensorRepresentative A S (simpleTensorRepresentative A T R)).data.object
    (simpleTensorRepresentative C U (simpleTensorRepresentative C V W)).data.object} {a b : ZMod 2}

noncomputable def tripleRightComparison (η : TensorComparison T R V W H K F a)
    (θ : TensorComparison S (simpleTensorRepresentative A T R) U (simpleTensorRepresentative C V W) E F N b) :
    TripleComparison S T R U V W E H K (tripleRightFunctor S T R U V W N) (a + b) :=
  ⟨tripleRightComparisonData S T R U V W η.data θ.data, tripleRightComparisonLaws η θ⟩

end RMod.Classification
