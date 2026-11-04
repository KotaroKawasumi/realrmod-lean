import RMod.Classification.Instances.SpanAssociator
import RMod.Classification.Instances.SpanSuperfunctorComposition

/-!
# Presenting the right product functor on the left triple spans

Compose with the identity span changes on the source and target. The
underlying ambient object and morphism operations remain those of the
supplied right product functor; its superlinear laws compose separately.
-/

set_option autoImplicit false

namespace RMod.Classification

variable {A C : WeaklyPointedSuperfusion.{0, 0}}
  (S T R : SimpleObject A) (U V W : SimpleObject C)

noncomputable def tripleRightFunctorData
    (N : SpanSuperfunctorData A C
      (simpleTensorRepresentative A S (simpleTensorRepresentative A T R)).data.object
      (simpleTensorRepresentative C U (simpleTensorRepresentative C V W)).data.object) :
    SpanSuperfunctorData A C
      (simpleTensorRepresentative A (simpleTensorRepresentative A S T) R).data.object
      (simpleTensorRepresentative C (simpleTensorRepresentative C U V) W).data.object :=
  SpanSuperfunctor.compData
    (SpanSuperfunctor.compData (tripleAssociatorSpanEquivalence A S T R).forwardFunctor.data N)
    (tripleAssociatorSpanEquivalence C U V W).backwardFunctor.data

theorem tripleRightFunctorLaws
    (N : SpanSuperfunctor A C
      (simpleTensorRepresentative A S (simpleTensorRepresentative A T R)).data.object
      (simpleTensorRepresentative C U (simpleTensorRepresentative C V W)).data.object) :
    SpanSuperfunctorLaws A C _ _ (tripleRightFunctorData S T R U V W N.data) :=
  SpanSuperfunctor.compLaws
    ((tripleAssociatorSpanEquivalence A S T R).forwardFunctor.comp N)
    (tripleAssociatorSpanEquivalence C U V W).backwardFunctor

noncomputable def tripleRightFunctor
    (N : SpanSuperfunctor A C
      (simpleTensorRepresentative A S (simpleTensorRepresentative A T R)).data.object
      (simpleTensorRepresentative C U (simpleTensorRepresentative C V W)).data.object) :
    SpanSuperfunctor A C
      (simpleTensorRepresentative A (simpleTensorRepresentative A S T) R).data.object
      (simpleTensorRepresentative C (simpleTensorRepresentative C U V) W).data.object :=
  ⟨tripleRightFunctorData S T R U V W N.data, tripleRightFunctorLaws S T R U V W N⟩

end RMod.Classification
