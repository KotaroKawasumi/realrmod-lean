import RMod.Classification.Instances.PullbackSpanGeneratorChange
import RMod.Classification.Instances.GaugeEvaluatedComponent
import RMod.Classification.Proofs.EquivalenceSupportMultiplication
import RMod.Classification.Proofs.SpanSuperfunctorExt

/-!
# The actual evaluation functors agree after changing generators

All membership changes retain the same ambient maps. The support equality
identifies the remaining evaluation indices. Extensionality of completed
superfunctors then gives equality, including their separate laws.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (s : Twist)
  (S T : SimpleObject (twistedPullback C hC s).toWeaklyPointedSuperfusion)
  (e : pullbackSimpleDegree C hC s S = pullbackSimpleDegree C hC s T)

theorem pullbackEvaluation_change_generator :
    (((pullbackSourceSpanChange C hC s S T e).forwardFunctor.comp
      (pullbackSpanEvaluationEquivalence C hC s T).forwardFunctor).comp
        (pullbackReferenceSpanChange C hC s T S e.symm).forwardFunctor) =
      (pullbackSpanEvaluationEquivalence C hC s S).forwardFunctor := by
  apply SpanSuperfunctor.ext_raw
  · intro X
    exact congrArg (fun k => (X.obj k).val) e.symm
  · intro X Y f
    exact congr_arg_heq f.hom e.symm

theorem equivalenceEvaluation_change_generator (t : Twist)
    (E : MonoidalSuperequivalence (twistedPullback C hC s).toWeaklyPointedSuperfusion
      (twistedPullback C hC t).toWeaklyPointedSuperfusion) :
    (((pullbackSourceSpanChange C hC s S T e).forwardFunctor.comp
      (equivalenceEvaluatedComponent C hC s t E T).forwardFunctor).comp
        (pullbackReferenceSpanChange C hC s T S e.symm).forwardFunctor) =
      (equivalenceEvaluatedComponent C hC s t E S).forwardFunctor := by
  have he : pullbackSimpleDegree C hC t (E.mapSimple T) =
      pullbackSimpleDegree C hC t (E.mapSimple S) := by
    rw [equivalenceSimpleDegree, equivalenceSimpleDegree, e]
  apply SpanSuperfunctor.ext_raw
  · intro X
    exact congrArg (fun k => (E.data.forward.obj X.obj k).val) he
  · intro X Y f
    exact congr_arg_heq (E.data.forward.map f.hom) he

end RMod.Classification
