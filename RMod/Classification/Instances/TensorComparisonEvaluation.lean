import RMod.Classification.Abstract.TensorComparison

/-!
# Evaluating a tensor comparison on its two generators

The evaluated maps are exactly the specified maps at that pair. Their
inverse, grading, and generator intertwining laws are specializations
of the corresponding laws of the full natural comparison.
-/

set_option autoImplicit false

namespace RMod.Classification.TensorComparison

variable {C D : WeaklyPointedSuperfusion.{0, 0}}
  {S T : SimpleObject C} {U V : SimpleObject D}

def evaluationData
    {E : SpanSuperfunctorData C D S.data.object U.data.object}
    {H : SpanSuperfunctorData C D T.data.object V.data.object}
    {N : SpanSuperfunctorData C D (simpleTensorRepresentative C S T).data.object
      (simpleTensorRepresentative D U V).data.object}
    (t : TensorComparisonData S T U V E H N) : TensorIntertwinerData S T U V E H N :=
  t.app (spanGenerator C S.data.object) (spanGenerator C T.data.object)

variable {E : SpanSuperfunctor C D S.data.object U.data.object}
  {H : SpanSuperfunctor C D T.data.object V.data.object}
  {N : SpanSuperfunctor C D (simpleTensorRepresentative C S T).data.object
    (simpleTensorRepresentative D U V).data.object} {a : ZMod 2}

theorem evaluationLaws (t : TensorComparison S T U V E H N a) :
    TensorIntertwinerLaws S T U V a (evaluationData t.data) where
  toIsoLaws := t.laws.iso _ _
  hom_grade := t.laws.hom_grade _ _
  inv_grade := t.laws.inv_grade _ _
  intertwines f g hf hg := t.laws.naturality f g hf hg

def evaluate (t : TensorComparison S T U V E H N a) : TensorIntertwiner S T U V E H N a :=
  ⟨evaluationData t.data, evaluationLaws t⟩

end RMod.Classification.TensorComparison
