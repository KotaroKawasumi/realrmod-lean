import RMod.Classification.Instances.PullbackEvaluation
import RMod.Classification.Proofs.PullbackSpanSupport
import RMod.Classification.Proofs.RestrictedSpanSurjective
import RMod.Classification.Proofs.SpanInverse

/-!
# Evaluation is a superlinear equivalence on a simple pullback component

Every object in the span has the generator's support, so extension by
zero is an explicit inverse on every Hom space and reflects grading.
Realizing parity lists supplies even object preimages. The existing
inverse construction bundles these data with all superlinear laws.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : Twist)
  (S : SimpleObject (twistedPullback C hC t).toWeaklyPointedSuperfusion)

noncomputable def pullbackSpanEvaluation : SpanSuperfunctor (twistedPullback C hC t).toWeaklyPointedSuperfusion
    ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩
    S.data.object (S.data.object (pullbackSimpleDegree C hC t S)).val :=
  (pullbackEvaluation C hC t (pullbackSimpleDegree C hC t S)).restrictSpan S.data.object

noncomputable def pullbackSpanEvaluationFullyFaithful :
    (pullbackSpanEvaluation C hC t S).toFunctor.FullyFaithful where
  preimage f := ObjectProperty.homMk (singleComponentHom C t.data (pullbackSimpleDegree C hC t S) f.hom)
  map_preimage f := ObjectProperty.hom_ext _ (singleComponentHom_at C t.data _ f.hom)
  preimage_map {X Y} f := ObjectProperty.hom_ext _
    (hom_ext_of_supported_source C t.data _ hC.toWeaklyPointedSuperfusionLaws
      (X := X.obj) (Y := Y.obj) (pullback_span_supported C hC t S X)
      (singleComponentHom C t.data (pullbackSimpleDegree C hC t S)
        (f.hom (pullbackSimpleDegree C hC t S))) f.hom
      (singleComponentHom_at C t.data _ (f.hom (pullbackSimpleDegree C hC t S))))

theorem pullbackSpanEvaluation_grade_iff
    {X Y : HomogeneousSpanCategory (twistedPullback C hC t).toWeaklyPointedSuperfusion S.data.object}
    {a : ZMod 2} (f : X ⟶ Y) :
    C.IsHomogeneous a ((pullbackSpanEvaluation C hC t S).toFunctor.map f).hom ↔
      (twistedPullback C hC t).data.IsHomogeneous a f.hom := by
  constructor
  · intro hf k
    by_cases hk : k = pullbackSimpleDegree C hC t S
    · subst k
      exact hf
    · have hz := hom_eq_zero_of_source hC.toWeaklyPointedSuperfusionLaws
        (pullback_span_supported C hC t S X k hk) (f.hom k)
      rw [hz]
      exact hC.grade_zero _ _ _
  · intro hf
    exact hf (pullbackSimpleDegree C hC t S)

noncomputable def pullbackSpanEvaluationPreimages : SpanPreimages (pullbackSpanEvaluation C hC t S) :=
  spanPreimages (pullbackSpanEvaluation C hC t S)
    ((pullbackEvaluation C hC t (pullbackSimpleDegree C hC t S)).restrictSpan_even_essSurj S.data.object)

noncomputable def pullbackSpanEvaluationEquivalenceData :
    SpanSuperequivalenceData (twistedPullback C hC t).toWeaklyPointedSuperfusion
      ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩
      S.data.object (S.data.object (pullbackSimpleDegree C hC t S)).val :=
  (pullbackSpanEvaluationPreimages C hC t S).underlyingEquivalence
    (pullbackSpanEvaluationFullyFaithful C hC t S)

theorem pullbackSpanEvaluationEquivalenceLaws :
    SpanSuperequivalenceLaws (twistedPullback C hC t).toWeaklyPointedSuperfusion
      ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩
      S.data.object (S.data.object (pullbackSimpleDegree C hC t S)).val
      (pullbackSpanEvaluationEquivalenceData C hC t S) :=
  (pullbackSpanEvaluationPreimages C hC t S).underlyingEquivalenceLaws
    (pullbackSpanEvaluationFullyFaithful C hC t S) (pullbackSpanEvaluation_grade_iff C hC t S)

noncomputable def pullbackSpanEvaluationEquivalence :
    SpanSuperequivalence (twistedPullback C hC t).toWeaklyPointedSuperfusion
      ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩
      S.data.object (S.data.object (pullbackSimpleDegree C hC t S)).val :=
  ⟨pullbackSpanEvaluationEquivalenceData C hC t S, pullbackSpanEvaluationEquivalenceLaws C hC t S⟩

end RMod.Classification
