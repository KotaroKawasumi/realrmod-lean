import RMod.Classification.Instances.ParityTripleReduction
import RMod.Classification.Proofs.TripleComparisonUniqueness
import RMod.Classification.Proofs.IsoScalarCancellation

/-!
# A unique real-unit ratio between even triple normalizations

Delete the common parity line and use the scalar theorem for homogeneous
triple comparisons. Cancellation of the specified inverse associator and
parity deletion recovers the equation for the original even maps.
-/

set_option autoImplicit false

namespace RMod.Classification.ParityTripleComparison

variable {A C : WeaklyPointedSuperfusion.{0, 0}}
  {S T R : SimpleObject A} {U V W : SimpleObject C} {p : Pi C.data}
  (E : SpanSuperequivalence A C S.data.object U.data.object)
  (H : SpanSuperequivalence A C T.data.object V.data.object)
  (K : SpanSuperequivalence A C R.data.object W.data.object)
  {N : SpanSuperfunctor A C
    (simpleTensorRepresentative A (simpleTensorRepresentative A S T) R).data.object
    (simpleTensorRepresentative C (simpleTensorRepresentative C U V) W).data.object} {a : ZMod 2}
  (η θ : ParityTripleComparison S T R U V W p E.forwardFunctor H.forwardFunctor K.forwardFunctor N a)

theorem comparison_eq_unique_unit_smul : ∃! r : ℝˣ,
    ∀ X Y Z, (θ.data.app X Y Z).hom = C.data.smul (r : ℝ) (η.data.app X Y Z).hom := by
  obtain ⟨r, hr, hu⟩ := TripleComparison.comparison_eq_unique_unit_smul E H K
    (parityTripleReduction η) (parityTripleReduction θ)
  refine ⟨r, ?_, ?_⟩
  · intro X Y Z
    have h := hr X Y Z
    exact iso_cancel_right_smul C.laws
      (p.laws.rightFactorDeletion_homogeneousIso C.laws _ a).toIsoLaws
      (iso_cancel_right_smul C.laws
        (EvenIsoLaws.assoc C.laws (E.forwardFunctor.data.obj X).obj (H.forwardFunctor.data.obj Y).obj
          (K.forwardFunctor.data.obj Z).obj).symm.toIsoLaws h)
  · intro s hs
    apply hu s
    intro X Y Z
    exact iso_comp_right_smul C.laws
      ((IsoData.assoc C.data (E.forwardFunctor.data.obj X).obj (H.forwardFunctor.data.obj Y).obj
        (K.forwardFunctor.data.obj Z).obj).symm C.data)
      (iso_comp_right_smul C.laws (p.data.rightFactorDeletion _ a) (hs X Y Z))

end RMod.Classification.ParityTripleComparison
