import RMod.Classification.Abstract.TripleComparison

/-!
# Evaluating a full triple comparison at its three generators

Use precisely its specified component isomorphism. Signed naturality
specializes to the pure triple endomorphism action, giving the already
defined generator intertwiner without any further choice of maps.
-/

set_option autoImplicit false

namespace RMod.Classification.TripleComparison

variable {A C : WeaklyPointedSuperfusion.{0, 0}}
  {S T R : SimpleObject A} {U V W : SimpleObject C}

def evaluationData
    {E : SpanSuperfunctorData A C S.data.object U.data.object}
    {H : SpanSuperfunctorData A C T.data.object V.data.object}
    {K : SpanSuperfunctorData A C R.data.object W.data.object}
    {N : SpanSuperfunctorData A C
      (simpleTensorRepresentative A (simpleTensorRepresentative A S T) R).data.object
      (simpleTensorRepresentative C (simpleTensorRepresentative C U V) W).data.object}
    (d : TripleComparisonData S T R U V W E H K N) : TripleIntertwinerData S T R U V W E H K N :=
  d.app (spanGenerator A S.data.object) (spanGenerator A T.data.object) (spanGenerator A R.data.object)

variable {E : SpanSuperfunctor A C S.data.object U.data.object}
  {H : SpanSuperfunctor A C T.data.object V.data.object}
  {K : SpanSuperfunctor A C R.data.object W.data.object}
  {N : SpanSuperfunctor A C
    (simpleTensorRepresentative A (simpleTensorRepresentative A S T) R).data.object
    (simpleTensorRepresentative C (simpleTensorRepresentative C U V) W).data.object} {a : ZMod 2}

theorem evaluationLaws (t : TripleComparison S T R U V W E H K N a) :
    TripleIntertwinerLaws S T R U V W a (evaluationData t.data) where
  toHomogeneousIsoLaws := t.laws.iso _ _ _
  intertwines f g h hf hg hh := t.laws.naturality f g h hf hg hh

def evaluate (t : TripleComparison S T R U V W E H K N a) : TripleIntertwiner S T R U V W E H K N a :=
  ⟨evaluationData t.data, evaluationLaws t⟩

end RMod.Classification.TripleComparison
