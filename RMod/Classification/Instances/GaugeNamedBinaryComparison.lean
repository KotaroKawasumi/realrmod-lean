import RMod.Classification.Instances.GaugeNamedComparison
import RMod.Classification.Instances.EquivalenceIndexedComparisons
import RMod.Classification.Instances.HomogeneousTensorIso
import RMod.Classification.Instances.PullbackSpanGeneratorChange
import RMod.Classification.Proofs.EquivalenceSupportMultiplication

/-!
# The changed binary comparison at named source degrees

View the tensor product in the selected component at g*h, retaining its
actual underlying family. Change its output and both inputs using the
same named component comparisons. The middle map is the given inverse
tensorator followed by target evaluation at phi(g)*phi(h).
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (s t : Twist)
  (E : MonoidalSuperequivalence (twistedPullback C hC s).toWeaklyPointedSuperfusion
    (twistedPullback C hC t).toWeaklyPointedSuperfusion)

noncomputable def pullbackNamedTensorSpanObj (g h : s.data.group)
    (X : HomogeneousSpanCategory (twistedPullback C hC s).toWeaklyPointedSuperfusion
      (pullbackDegreeSimple C hC s g).data.object)
    (Y : HomogeneousSpanCategory (twistedPullback C hC s).toWeaklyPointedSuperfusion
      (pullbackDegreeSimple C hC s h).data.object) :
    HomogeneousSpanCategory (twistedPullback C hC s).toWeaklyPointedSuperfusion
      (pullbackDegreeSimple C hC s (g * h)).data.object :=
  (pullbackSourceSpanChange C hC s
    (simpleTensorRepresentative (twistedPullback C hC s).toWeaklyPointedSuperfusion
      (pullbackDegreeSimple C hC s g) (pullbackDegreeSimple C hC s h))
    (pullbackDegreeSimple C hC s (g * h)) (by
      rw [pullbackSimpleDegree_tensor, pullbackSimpleDegree_placed,
        pullbackSimpleDegree_placed, pullbackSimpleDegree_placed])).forwardFunctor.data.obj
    (spanTensorObj (twistedPullback C hC s).toWeaklyPointedSuperfusion
      (pullbackDegreeSimple C hC s g) (pullbackDegreeSimple C hC s h) X Y)

noncomputable def equivalenceNamedChangedComparisonData (g h : s.data.group)
    (X : HomogeneousSpanCategory (twistedPullback C hC s).toWeaklyPointedSuperfusion
      (pullbackDegreeSimple C hC s g).data.object)
    (Y : HomogeneousSpanCategory (twistedPullback C hC s).toWeaklyPointedSuperfusion
      (pullbackDegreeSimple C hC s h).data.object) :
    IsoData C.toWeaklyPointedSuperfusionData
      (convolutionObj C hC s.data X.obj Y.obj (g * h)).val
      (C.tensorObj (X.obj g).val (Y.obj h).val) :=
  (((equivalenceNamedComparisonData C hC s t E (g * h)
      (pullbackNamedTensorSpanObj C hC s g h X Y)).symm C.toWeaklyPointedSuperfusionData).trans
    C.toWeaklyPointedSuperfusionData
      (equivalenceIndexedComparisonData C hC s t E X.obj Y.obj
        (equivalenceGaugePhi C hC s t E g) (equivalenceGaugePhi C hC s t E h)
        (equivalenceGaugePhi C hC s t E (g * h))
        (map_mul (equivalenceGaugePhi C hC s t E) g h).symm)).trans
    C.toWeaklyPointedSuperfusionData
      ((equivalenceNamedComparisonData C hC s t E g X).homogeneousTensor C.toWeaklyPointedSuperfusionData
        (equivalenceGaugeLambda C hC s t E g) (equivalenceGaugeLambda C hC s t E h)
        (equivalenceNamedComparisonData C hC s t E h Y))

end RMod.Classification
