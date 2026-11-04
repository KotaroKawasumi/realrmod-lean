import RMod.Classification.Proofs.GaugeNamedBinaryMaps

/-!
# The same binary scalar after naming the group coordinates

Transport the already proved comparison identity through the endpoint
equalities. The named changed tensorator has precisely the originally
retained ratio, on every pair of component objects.
-/

set_option autoImplicit false

namespace RMod.Classification

theorem equivalenceNamedComparison_ratio
    (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (s t : Twist)
    (E : MonoidalSuperequivalence (twistedPullback C hC s).toWeaklyPointedSuperfusion
      (twistedPullback C hC t).toWeaklyPointedSuperfusion) (g h : s.data.group)
    (X : HomogeneousSpanCategory (twistedPullback C hC s).toWeaklyPointedSuperfusion
      (pullbackDegreeSimple C hC s g).data.object)
    (Y : HomogeneousSpanCategory (twistedPullback C hC s).toWeaklyPointedSuperfusion
      (pullbackDegreeSimple C hC s h).data.object) :
    (equivalenceNamedChangedComparisonData C hC s t E g h X Y).hom =
      C.smul (equivalenceGaugeRatio C hC s t E g h).val
        (convolutionIndexedComparisonData C hC s.data X.obj Y.obj g h (g * h) rfl).hom := by
  apply eq_of_heq
  refine (equivalenceChangedTensorComparison_named_heq C hC s t E g h X Y).symm.trans
    ((heq_of_eq (equivalenceGaugeRatio_spec C hC s t E g h X Y)).trans ?_)
  exact rawHom_smul_heq (C := C.toWeaklyPointedSuperfusionData)
    (congrArg (fun j => (convolutionObj C hC s.data X.obj Y.obj j).val)
      (pullbackDegreeSimple_tensorDegree C hC s g h))
    (congrArg₂ C.tensorObj
      (congrArg (fun j => (X.obj j).val) (pullbackSimpleDegree_placed C hC s g))
      (congrArg (fun j => (Y.obj j).val) (pullbackSimpleDegree_placed C hC s h)))
    (equivalenceGaugeRatio C hC s t E g h).val (pullbackTensorComparison_named_heq C hC s g h X Y)

end RMod.Classification
