import RMod.Classification.Proofs.TensorGeneratorProduct
import RMod.Classification.Proofs.SpanNaturalIsoExistence
import RMod.Classification.Instances.TensorIntertwiner

/-!
# Existence of the parity of a tensor comparison

For any independently prescribed equivalence on the product component,
compare it naturally with the equivalence realizing the tensor action.
The component at the tensor generator gives an invertible signed
intertwiner, in the parity supplied by super Skolem--Noether.
-/

set_option autoImplicit false

namespace RMod.Classification

theorem exists_tensorIntertwiner (C D : PiSuperfusion.{0, 0})
    (S T : SimpleObject C.toWeaklyPointedSuperfusion)
    (U V : SimpleObject D.toWeaklyPointedSuperfusion)
    (E : SpanSuperequivalence C.toWeaklyPointedSuperfusion D.toWeaklyPointedSuperfusion
      S.data.object U.data.object)
    (H : SpanSuperequivalence C.toWeaklyPointedSuperfusion D.toWeaklyPointedSuperfusion
      T.data.object V.data.object)
    (N : SpanSuperequivalence C.toWeaklyPointedSuperfusion D.toWeaklyPointedSuperfusion
      (simpleTensorRepresentative C.toWeaklyPointedSuperfusion S T).data.object
      (simpleTensorRepresentative D.toWeaklyPointedSuperfusion U V).data.object) :
    ∃ a : ZMod 2, Nonempty (TensorIntertwiner S T U V
      E.forwardFunctor H.forwardFunctor N.forwardFunctor a) := by
  obtain ⟨M, e, he, hm⟩ := exists_tensorGeneratorComparison_in_product C D S T U V E H
  obtain ⟨a, ⟨η⟩⟩ := exists_spanNaturalIso
    (simpleTensorRepresentative C.toWeaklyPointedSuperfusion S T).laws.simple
    (simpleTensorRepresentative D.toWeaklyPointedSuperfusion U V).laws.simple N M
  exact ⟨a, ⟨⟨tensorIntertwinerComparisonData S T U V η.data e,
    tensorIntertwinerComparisonLaws S T U V η e he (fun f g => hm f.hom g.hom)⟩⟩⟩

end RMod.Classification
