import RMod.Classification.Instances.GaugeIndexedBinaryComparison
import RMod.Classification.Proofs.GaugeNamedBinaryRatio

/-!
# The extracted binary ratio with an independent product index

Equality elimination reduces to the proved named comparison formula.
Proof irrelevance retains exactly the same component object and maps.
-/

set_option autoImplicit false

namespace RMod.Classification

theorem equivalenceIndexedComparison_ratio
    (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (s t : Twist)
    (E : MonoidalSuperequivalence (twistedPullback C hC s).toWeaklyPointedSuperfusion
      (twistedPullback C hC t).toWeaklyPointedSuperfusion)
    (g h u : s.data.group) (e : g * h = u)
    (X : HomogeneousSpanCategory (twistedPullback C hC s).toWeaklyPointedSuperfusion
      (pullbackDegreeSimple C hC s g).data.object)
    (Y : HomogeneousSpanCategory (twistedPullback C hC s).toWeaklyPointedSuperfusion
      (pullbackDegreeSimple C hC s h).data.object) :
    (equivalenceIndexedChangedComparisonData C hC s t E g h u e X Y).hom =
      C.smul (equivalenceGaugeRatio C hC s t E g h).val
        (convolutionIndexedComparisonData C hC s.data X.obj Y.obj g h u e).hom := by
  cases e
  exact equivalenceNamedComparison_ratio C hC s t E g h X Y

end RMod.Classification
