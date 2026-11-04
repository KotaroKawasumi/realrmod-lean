import RMod.Classification.Instances.GaugeEvaluatedComponent
import RMod.Classification.Proofs.PullbackUnitLabel

/-!
# The selected component comparison at its named group coordinate

The image coordinate is definitionally phi(g). The direct evaluation
coordinate is identified with g by the support theorem for the placed
simple. Append just that equality map to the retained comparison; its
inverse is retained in the reverse order.
-/

set_option autoImplicit false

namespace RMod.Classification

noncomputable def equivalenceNamedComparisonData
    (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (s t : Twist)
    (E : MonoidalSuperequivalence (twistedPullback C hC s).toWeaklyPointedSuperfusion
      (twistedPullback C hC t).toWeaklyPointedSuperfusion) (g : s.data.group)
    (X : HomogeneousSpanCategory (twistedPullback C hC s).toWeaklyPointedSuperfusion
      (pullbackDegreeSimple C hC s g).data.object) :
    IsoData C.toWeaklyPointedSuperfusionData
      (E.data.forward.obj X.obj (equivalenceGaugePhi C hC s t E g)).val (X.obj g).val :=
  (⟨((equivalenceComponentComparison C hC s t E g).data.app X).hom,
    ((equivalenceComponentComparison C hC s t E g).data.inv.app X).hom⟩ : IsoData C.toWeaklyPointedSuperfusionData _ _).trans
    C.toWeaklyPointedSuperfusionData
      (IsoData.ofEq C.toWeaklyPointedSuperfusionData
        (congrArg (fun j => (X.obj j).val) (pullbackSimpleDegree_placed C hC s g)))

end RMod.Classification
