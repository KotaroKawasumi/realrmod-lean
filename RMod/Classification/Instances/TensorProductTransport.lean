import RMod.Classification.Instances.SpanChange
import RMod.Classification.Instances.SpanEquivalenceComposition
import RMod.Classification.Instances.SimpleTensorRepresentative

/-! # Presenting a component functor on tensor-product generators -/

set_option autoImplicit false

namespace RMod.Classification

variable {A C : WeaklyPointedSuperfusion.{0, 0}}

noncomputable def tensorProductTransport
    (S T R : SimpleObject A) (U V W : SimpleObject C)
    (E : SpanSuperequivalence A C R.data.object W.data.object)
    (hA : SameParityOrbit A.data (simpleTensorRepresentative A S T).data.object R.data.object)
    (hC : SameParityOrbit C.data (simpleTensorRepresentative C U V).data.object W.data.object) :
    SpanSuperequivalence A C (simpleTensorRepresentative A S T).data.object
      (simpleTensorRepresentative C U V).data.object :=
  ((spanChangeSuperequivalence A (inHomogeneousSpan_congr_generator A
      (simpleTensorRepresentative A S T).laws.simple R.laws.simple hA)).trans E).trans
    (spanChangeSuperequivalence C (inHomogeneousSpan_congr_generator C
      W.laws.simple (simpleTensorRepresentative C U V).laws.simple hC.symm))

end RMod.Classification
