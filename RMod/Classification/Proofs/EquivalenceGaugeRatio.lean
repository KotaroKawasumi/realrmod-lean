import RMod.Classification.Instances.EquivalenceGaugeRatio

/-!
# The extracted binary ratio applies on every pair of objects

The tensor-comparison uniqueness theorem extends its generator scalar
through all homogeneous sums. Its specification therefore identifies
the actual natural comparison families, not just one simple-object map.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (s t : Twist)
  (E : MonoidalSuperequivalence (twistedPullback C hC s).toWeaklyPointedSuperfusion
    (twistedPullback C hC t).toWeaklyPointedSuperfusion)

theorem equivalenceGaugeRatio_spec (g h : s.data.group)
    (X : HomogeneousSpanCategory (twistedPullback C hC s).toWeaklyPointedSuperfusion
      (pullbackDegreeSimple C hC s g).data.object)
    (Y : HomogeneousSpanCategory (twistedPullback C hC s).toWeaklyPointedSuperfusion
      (pullbackDegreeSimple C hC s h).data.object) :
    ((equivalenceChangedTensorComparison C hC s t E g h).data.app X Y).hom =
      C.smul (equivalenceGaugeRatio C hC s t E g h).val
        ((pullbackTensorComparison C hC s (pullbackDegreeSimple C hC s g)
          (pullbackDegreeSimple C hC s h)).data.app X Y).hom :=
  (Classical.choose_spec (TensorComparison.comparison_eq_unique_unit_smul
    (S := pullbackDegreeSimple C hC s g) (T := pullbackDegreeSimple C hC s h)
    (U := pullbackReferenceSimple C hC s (pullbackDegreeSimple C hC s g))
    (V := pullbackReferenceSimple C hC s (pullbackDegreeSimple C hC s h))
    (pullbackSpanEvaluationEquivalence C hC s (pullbackDegreeSimple C hC s g))
    (pullbackSpanEvaluationEquivalence C hC s (pullbackDegreeSimple C hC s h))
    (pullbackTensorComparison C hC s (pullbackDegreeSimple C hC s g) (pullbackDegreeSimple C hC s h))
    (equivalenceChangedTensorComparison C hC s t E g h))).1 X Y

theorem equivalenceGaugeRatio_unique (g h : s.data.group) (r : ℝˣ)
    (hr : ∀ X Y, ((equivalenceChangedTensorComparison C hC s t E g h).data.app X Y).hom =
      C.smul r.val ((pullbackTensorComparison C hC s (pullbackDegreeSimple C hC s g)
        (pullbackDegreeSimple C hC s h)).data.app X Y).hom) : r = equivalenceGaugeRatio C hC s t E g h :=
  (Classical.choose_spec (TensorComparison.comparison_eq_unique_unit_smul
    (S := pullbackDegreeSimple C hC s g) (T := pullbackDegreeSimple C hC s h)
    (U := pullbackReferenceSimple C hC s (pullbackDegreeSimple C hC s g))
    (V := pullbackReferenceSimple C hC s (pullbackDegreeSimple C hC s h))
    (pullbackSpanEvaluationEquivalence C hC s (pullbackDegreeSimple C hC s g))
    (pullbackSpanEvaluationEquivalence C hC s (pullbackDegreeSimple C hC s h))
    (pullbackTensorComparison C hC s (pullbackDegreeSimple C hC s g) (pullbackDegreeSimple C hC s h))
    (equivalenceChangedTensorComparison C hC s t E g h))).2 r hr

end RMod.Classification
