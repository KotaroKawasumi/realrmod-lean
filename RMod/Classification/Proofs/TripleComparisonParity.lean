import RMod.Classification.Instances.TripleComparisonEvaluation
import RMod.Classification.Proofs.TripleIntertwinerLines

/-! # Full triple comparisons have a unique possible degree -/

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

include E H K η θ

theorem parity_unique : a = b := TripleIntertwiner.parity_unique E H K η.evaluate θ.evaluate

theorem generator_eq_unique_unit_smul : ∃! r : ℝˣ,
    θ.evaluate.data.hom = C.data.smul (r : ℝ) η.evaluate.data.hom :=
  TripleIntertwiner.comparison_eq_unique_unit_smul E H K η.evaluate θ.evaluate

end RMod.Classification.TripleComparison
