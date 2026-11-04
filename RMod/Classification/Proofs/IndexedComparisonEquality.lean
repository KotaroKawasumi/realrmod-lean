import RMod.Classification.Instances.EquivalenceIndexedComparisons

/-!
# Indexed comparison maps are retained under equal indices

Changing input and output degree names only changes the endpoint types.
Once those indices are identified, the parity deletion and all specified
inverse tensorator maps are literally the original maps.
-/

set_option autoImplicit false

namespace RMod.Classification

theorem convolutionIndexedComparison_hom_heq
    (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData)
    (X Y : PullbackObj C t) {g g' h h' u u' : t.group}
    (eg : g = g') (eh : h = h') (eu : u = u') (e : g * h = u) (e' : g' * h' = u') :
    HEq (convolutionIndexedComparisonData C hC t X Y g h u e).hom
      (convolutionIndexedComparisonData C hC t X Y g' h' u' e').hom := by
  cases eg
  cases eh
  cases eu
  rfl

theorem equivalenceIndexedComparison_hom_heq
    (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (s t : Twist)
    (E : MonoidalSuperequivalence (twistedPullback C hC s).toWeaklyPointedSuperfusion
      (twistedPullback C hC t).toWeaklyPointedSuperfusion)
    (X Y : PullbackObj C s.data) {g g' h h' u u' : t.data.group}
    (eg : g = g') (eh : h = h') (eu : u = u') (e : g * h = u) (e' : g' * h' = u') :
    HEq (equivalenceIndexedComparisonData C hC s t E X Y g h u e).hom
      (equivalenceIndexedComparisonData C hC s t E X Y g' h' u' e').hom := by
  cases eg
  cases eh
  cases eu
  rfl

end RMod.Classification
