import RMod.Classification.Proofs.GaugeIndexedBinaryRatio
import RMod.Classification.Proofs.EquivalenceTensorComparison
import RMod.Classification.Proofs.ConvolutionIndexedComparisons

/-!
# Supports and degrees of the named binary comparisons

Objects in the component at g and their images have supports g and
phi(g). The retained inverse tensorator is even, so its target binary
comparison has the target nu degree. The changed comparison has the
source nu degree by the already proved scalar identity.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (s t : Twist)
  (E : MonoidalSuperequivalence (twistedPullback C hC s).toWeaklyPointedSuperfusion
    (twistedPullback C hC t).toWeaklyPointedSuperfusion)

theorem pullback_named_span_supported (g : s.data.group)
    (X : HomogeneousSpanCategory (twistedPullback C hC s).toWeaklyPointedSuperfusion
      (pullbackDegreeSimple C hC s g).data.object)
    (l : s.data.group) (hl : l ≠ g) : C.id (X.obj l).val = C.zero :=
  pullback_span_supported C hC s (pullbackDegreeSimple C hC s g) X l
    (fun e => hl (e.trans (pullbackSimpleDegree_placed C hC s g)))

theorem equivalence_named_span_supported (g : s.data.group)
    (X : HomogeneousSpanCategory (twistedPullback C hC s).toWeaklyPointedSuperfusion
      (pullbackDegreeSimple C hC s g).data.object)
    (l : t.data.group) (hl : l ≠ equivalenceGaugePhi C hC s t E g) :
    C.id (E.data.forward.obj X.obj l).val = C.zero :=
  pullback_span_supported C hC t (E.mapSimple (pullbackDegreeSimple C hC s g))
    ((E.spanRestriction (pullbackDegreeSimple C hC s g)).forwardFunctor.data.obj X) l hl

theorem equivalenceIndexedComponentComparison_homogeneousIso
    (g h u : s.data.group) (e : g * h = u)
    (X : HomogeneousSpanCategory (twistedPullback C hC s).toWeaklyPointedSuperfusion
      (pullbackDegreeSimple C hC s g).data.object)
    (Y : HomogeneousSpanCategory (twistedPullback C hC s).toWeaklyPointedSuperfusion
      (pullbackDegreeSimple C hC s h).data.object) :
    HomogeneousIsoLaws C.toWeaklyPointedSuperfusionData
      (t.data.nu (equivalenceGaugePhi C hC s t E g) (equivalenceGaugePhi C hC s t E h))
      (equivalenceIndexedComparisonData C hC s t E X.obj Y.obj
        (equivalenceGaugePhi C hC s t E g) (equivalenceGaugePhi C hC s t E h)
        (equivalenceGaugePhi C hC s t E u)
        ((map_mul (equivalenceGaugePhi C hC s t E) g h).symm.trans
          (congrArg (equivalenceGaugePhi C hC s t E) e))) := by
  have he := (equivalenceTensoratorComponent_evenIso C hC s t E X.obj Y.obj
    (equivalenceGaugePhi C hC s t E u)).homogeneous.trans hC.toWeaklyPointedSuperfusionLaws
    (convolutionIndexedComparison_homogeneousIso C hC t.data
      (E.data.forward.obj X.obj) (E.data.forward.obj Y.obj)
      (equivalenceGaugePhi C hC s t E g) (equivalenceGaugePhi C hC s t E h)
      (equivalenceGaugePhi C hC s t E u)
      ((map_mul (equivalenceGaugePhi C hC s t E) g h).symm.trans
        (congrArg (equivalenceGaugePhi C hC s t E) e))
      (equivalence_named_span_supported C hC s t E g X))
  rw [zero_add] at he
  exact he

theorem equivalenceIndexedChangedComparison_hom_grade
    (g h u : s.data.group) (e : g * h = u)
    (X : HomogeneousSpanCategory (twistedPullback C hC s).toWeaklyPointedSuperfusion
      (pullbackDegreeSimple C hC s g).data.object)
    (Y : HomogeneousSpanCategory (twistedPullback C hC s).toWeaklyPointedSuperfusion
      (pullbackDegreeSimple C hC s h).data.object) :
    C.IsHomogeneous (s.data.nu g h) (equivalenceIndexedChangedComparisonData C hC s t E g h u e X Y).hom := by
  rw [equivalenceIndexedComparison_ratio]
  exact hC.grade_smul _ _ (convolutionIndexedComparison_homogeneousIso C hC s.data X.obj Y.obj
    g h u e (pullback_named_span_supported C hC s g X)).hom_grade

end RMod.Classification
