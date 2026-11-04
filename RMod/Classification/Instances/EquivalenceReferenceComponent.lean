import RMod.Classification.Instances.RestrictedSpanEquivalence
import RMod.Classification.Instances.PullbackSpanEvaluation
import RMod.Classification.Instances.SpanEquivalenceComposition
import RMod.Classification.Instances.SpanEquivalenceSymmetry
import RMod.Classification.Instances.SpanChange
import RMod.Classification.Proofs.EquivalenceComponentTypes

/-!
# The reference-component autoequivalence induced by an arbitrary equivalence

Move from the reference span into the source model using inverse
evaluation, apply the given restricted equivalence, and evaluate in the
target model. Equal intrinsic types identify the two reference spans by
the identity on every ambient object and morphism. Thus the result is an
actual superlinear autoequivalence to which comparison-line uniqueness
applies.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (s t : Twist)
  (E : MonoidalSuperequivalence (twistedPullback C hC s).toWeaklyPointedSuperfusion
    (twistedPullback C hC t).toWeaklyPointedSuperfusion)
  (S : SimpleObject (twistedPullback C hC s).toWeaklyPointedSuperfusion)

noncomputable def equivalenceReferenceComponent :
    SpanSuperequivalence
      ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩
      ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩
      (S.data.object (pullbackSimpleDegree C hC s S)).val
      (S.data.object (pullbackSimpleDegree C hC s S)).val :=
  (((pullbackSpanEvaluationEquivalence C hC s S).symm.trans (E.spanRestriction S)).trans
    (pullbackSpanEvaluationEquivalence C hC t (E.mapSimple S))).trans
      (spanChangeSuperequivalence ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩
        (fun X => (inHomogeneousSpan_congr_generator
          ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩
          (pullbackSimpleDegree_simple C hC s S) (pullbackSimpleDegree_simple C hC t (E.mapSimple S))
          (equivalenceComponentGenerators_sameOrbit C hC s t E S) X).symm))

end RMod.Classification
