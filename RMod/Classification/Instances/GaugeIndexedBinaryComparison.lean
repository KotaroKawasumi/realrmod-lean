import RMod.Classification.Instances.GaugeNamedBinaryComparison

/-!
# A named binary comparison with an independently identified product

Keep the product degree u with its witness g*h=u. This lets the two
associativity routes use the same final component and comparison even
when their intermediate product expressions have different parentheses.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (s t : Twist)
  (E : MonoidalSuperequivalence (twistedPullback C hC s).toWeaklyPointedSuperfusion
    (twistedPullback C hC t).toWeaklyPointedSuperfusion)

noncomputable def pullbackIndexedTensorSpanObj (g h u : s.data.group) (e : g * h = u)
    (X : HomogeneousSpanCategory (twistedPullback C hC s).toWeaklyPointedSuperfusion
      (pullbackDegreeSimple C hC s g).data.object)
    (Y : HomogeneousSpanCategory (twistedPullback C hC s).toWeaklyPointedSuperfusion
      (pullbackDegreeSimple C hC s h).data.object) :
    HomogeneousSpanCategory (twistedPullback C hC s).toWeaklyPointedSuperfusion
      (pullbackDegreeSimple C hC s u).data.object :=
  (pullbackSourceSpanChange C hC s
    (simpleTensorRepresentative (twistedPullback C hC s).toWeaklyPointedSuperfusion
      (pullbackDegreeSimple C hC s g) (pullbackDegreeSimple C hC s h))
    (pullbackDegreeSimple C hC s u) (by
      rw [pullbackSimpleDegree_tensor, pullbackSimpleDegree_placed,
        pullbackSimpleDegree_placed, pullbackSimpleDegree_placed]
      exact e)).forwardFunctor.data.obj
    (spanTensorObj (twistedPullback C hC s).toWeaklyPointedSuperfusion
      (pullbackDegreeSimple C hC s g) (pullbackDegreeSimple C hC s h) X Y)

noncomputable def equivalenceIndexedChangedComparisonData (g h u : s.data.group) (e : g * h = u)
    (X : HomogeneousSpanCategory (twistedPullback C hC s).toWeaklyPointedSuperfusion
      (pullbackDegreeSimple C hC s g).data.object)
    (Y : HomogeneousSpanCategory (twistedPullback C hC s).toWeaklyPointedSuperfusion
      (pullbackDegreeSimple C hC s h).data.object) :
    IsoData C.toWeaklyPointedSuperfusionData
      (convolutionObj C hC s.data X.obj Y.obj u).val (C.tensorObj (X.obj g).val (Y.obj h).val) :=
  (((equivalenceNamedComparisonData C hC s t E u
      (pullbackIndexedTensorSpanObj C hC s g h u e X Y)).symm C.toWeaklyPointedSuperfusionData).trans
    C.toWeaklyPointedSuperfusionData
      (equivalenceIndexedComparisonData C hC s t E X.obj Y.obj
        (equivalenceGaugePhi C hC s t E g) (equivalenceGaugePhi C hC s t E h)
        (equivalenceGaugePhi C hC s t E u)
        ((map_mul (equivalenceGaugePhi C hC s t E) g h).symm.trans
          (congrArg (equivalenceGaugePhi C hC s t E) e)))).trans
    C.toWeaklyPointedSuperfusionData
      ((equivalenceNamedComparisonData C hC s t E g X).homogeneousTensor C.toWeaklyPointedSuperfusionData
        (equivalenceGaugeLambda C hC s t E g) (equivalenceGaugeLambda C hC s t E h)
        (equivalenceNamedComparisonData C hC s t E h Y))

end RMod.Classification
