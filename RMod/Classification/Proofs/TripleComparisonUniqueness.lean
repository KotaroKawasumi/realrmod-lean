import RMod.Classification.Proofs.TripleComparisonExt
import RMod.Classification.Proofs.TripleComparisonParity

/-!
# The scalar-unit ratio is uniform on all triples

Full faithfulness on the three generators fixes the parity and the
unique nonzero real scalar. The matrix extension theorem propagates it
to the entire comparison family, including arbitrary finite sums.
-/

set_option autoImplicit false

namespace RMod.Classification.TripleComparison

variable {A C : WeaklyPointedSuperfusion.{0, 0}}
  {S T R : SimpleObject A} {U V W : SimpleObject C}
  (E : SpanSuperequivalence A C S.data.object U.data.object)
  (H : SpanSuperequivalence A C T.data.object V.data.object)
  (K : SpanSuperequivalence A C R.data.object W.data.object)
  {N : SpanSuperfunctor A C
    (simpleTensorRepresentative A (simpleTensorRepresentative A S T) R).data.object
    (simpleTensorRepresentative C (simpleTensorRepresentative C U V) W).data.object} {a b : ZMod 2}
  (η : TripleComparison S T R U V W E.forwardFunctor H.forwardFunctor K.forwardFunctor N a)
  (θ : TripleComparison S T R U V W E.forwardFunctor H.forwardFunctor K.forwardFunctor N b)

theorem comparison_eq_unique_unit_smul : ∃! r : ℝˣ,
    ∀ X Y Z, (θ.data.app X Y Z).hom = C.data.smul (r : ℝ) (η.data.app X Y Z).hom := by
  have hab := parity_unique E H K η θ
  subst b
  obtain ⟨r, hr, hu⟩ := generator_eq_unique_unit_smul E H K η θ
  refine ⟨r, hom_eq_smul_of_generator θ η (r : ℝ) hr, ?_⟩
  intro s hs
  exact hu s (hs (spanGenerator A S.data.object) (spanGenerator A T.data.object)
    (spanGenerator A R.data.object))

end RMod.Classification.TripleComparison
