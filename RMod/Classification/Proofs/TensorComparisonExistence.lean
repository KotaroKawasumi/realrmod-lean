import RMod.Classification.Instances.TensorComparisonExtension
import RMod.Classification.Proofs.TensorComparisonUniqueness
import RMod.Classification.Proofs.TensorIntertwinerExistence

/-!
# Existence and unique parity of full multiplication comparisons

The constructed generator intertwiner extends to an actual invertible
homogeneous natural comparison on both components. Evaluation proves
that its degree is the only possible degree for any such comparison.
-/

set_option autoImplicit false

namespace RMod.Classification

theorem exists_unique_tensorComparison_parity (C D : PiSuperfusion.{0, 0})
    (S T : SimpleObject C.toWeaklyPointedSuperfusion)
    (U V : SimpleObject D.toWeaklyPointedSuperfusion)
    (E : SpanSuperequivalence C.toWeaklyPointedSuperfusion D.toWeaklyPointedSuperfusion
      S.data.object U.data.object)
    (H : SpanSuperequivalence C.toWeaklyPointedSuperfusion D.toWeaklyPointedSuperfusion
      T.data.object V.data.object)
    (N : SpanSuperequivalence C.toWeaklyPointedSuperfusion D.toWeaklyPointedSuperfusion
      (simpleTensorRepresentative C.toWeaklyPointedSuperfusion S T).data.object
      (simpleTensorRepresentative D.toWeaklyPointedSuperfusion U V).data.object) :
    ∃! a : ZMod 2, Nonempty (TensorComparison S T U V
      E.forwardFunctor H.forwardFunctor N.forwardFunctor a) := by
  obtain ⟨a, ⟨t⟩⟩ := exists_tensorIntertwiner C D S T U V E H N
  refine ⟨a, ⟨tensorComparisonExtension t⟩, ?_⟩
  rintro b ⟨θ⟩
  exact TensorComparison.parity_unique E H θ (tensorComparisonExtension t)

end RMod.Classification
