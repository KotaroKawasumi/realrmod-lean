import RMod.Classification.Proofs.TensorComparisonExtensionNaturality

/-!
# Completed homogeneous tensor comparisons

Bundle the objectwise matrix sums with their inverse, grading, and
signed naturality laws. This turns a generator intertwiner into a
comparison on the entire pair of homogeneous components.
-/

set_option autoImplicit false

namespace RMod.Classification

variable {C D : WeaklyPointedSuperfusion.{0, 0}}
  {S T : SimpleObject C} {U V : SimpleObject D}
  {E : SpanSuperfunctor C D S.data.object U.data.object}
  {H : SpanSuperfunctor C D T.data.object V.data.object}
  {N : SpanSuperfunctor C D (simpleTensorRepresentative C S T).data.object
    (simpleTensorRepresentative D U V).data.object} {a : ZMod 2}

noncomputable def tensorComparisonExtension (t : TensorIntertwiner S T U V E H N a) :
    TensorComparison S T U V E H N a :=
  ⟨tensorComparisonExtensionData S T U V E.data H.data N.data a t.data,
    tensorComparisonExtensionLaws t⟩

end RMod.Classification
