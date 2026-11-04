import RMod.Classification.Proofs.TensorComparisonExt
import RMod.Classification.Proofs.TensorIntertwinerLines

/-!
# Unique parity and scalar-unit ratios of full tensor comparisons

Evaluation reduces the parity question to the generator theorem. Its
unique real-unit ratio extends to all pairs by the mapped matrix units.
Thus both statements concern actual natural comparison families.
-/

set_option autoImplicit false

namespace RMod.Classification.TensorComparison

variable {C D : WeaklyPointedSuperfusion.{0, 0}}
  {S T : SimpleObject C} {U V : SimpleObject D}
  (E : SpanSuperequivalence C D S.data.object U.data.object)
  (H : SpanSuperequivalence C D T.data.object V.data.object)
  {N : SpanSuperfunctor C D (simpleTensorRepresentative C S T).data.object
    (simpleTensorRepresentative D U V).data.object} {a b : ZMod 2}
  (η : TensorComparison S T U V E.forwardFunctor H.forwardFunctor N a)
  (θ : TensorComparison S T U V E.forwardFunctor H.forwardFunctor N b)

include E H η θ in
theorem parity_unique : a = b := TensorIntertwiner.parity_unique E H η.evaluate θ.evaluate

theorem comparison_eq_unique_unit_smul : ∃! r : ℝˣ,
    ∀ X Y, (θ.data.app X Y).hom = D.data.smul (r : ℝ) (η.data.app X Y).hom := by
  have hab := parity_unique E H η θ
  subst b
  obtain ⟨r, hr, hu⟩ := TensorIntertwiner.comparison_eq_unique_unit_smul E H η.evaluate θ.evaluate
  refine ⟨r, hom_eq_smul_of_generator θ η (r : ℝ) hr, ?_⟩
  intro s hs
  exact hu s (hs (spanGenerator C S.data.object) (spanGenerator C T.data.object))

end RMod.Classification.TensorComparison
