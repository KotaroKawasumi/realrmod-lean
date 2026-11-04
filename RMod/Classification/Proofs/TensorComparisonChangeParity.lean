import RMod.Classification.Instances.TensorComparisonChange
import RMod.Classification.Proofs.TensorComparisonUniqueness

/-!
# Uniqueness forces the parity change equation for binary comparisons

After transporting all three component functors, compare with any binary
comparison for those same functors. Full faithfulness of the two input
equivalences forces its degree to differ by the three component parities.
The scalar comparison theorem can then be applied to these actual maps.
-/

set_option autoImplicit false

namespace RMod.Classification.TensorComparison

theorem component_change_parity {A C : WeaklyPointedSuperfusion.{0, 0}}
    {S T : SimpleObject A} {U V : SimpleObject C}
    {E : SpanSuperfunctor A C S.data.object U.data.object}
    {H : SpanSuperfunctor A C T.data.object V.data.object}
    (E' : SpanSuperequivalence A C S.data.object U.data.object)
    (H' : SpanSuperequivalence A C T.data.object V.data.object)
    {N N' : SpanSuperfunctor A C (simpleTensorRepresentative A S T).data.object
      (simpleTensorRepresentative C U V).data.object}
    {a b c d c' : ZMod 2} (κ : TensorComparison S T U V E H N c)
    (i : SpanHomogeneousNatIso E E'.forwardFunctor a)
    (j : SpanHomogeneousNatIso H H'.forwardFunctor b) (n : SpanHomogeneousNatIso N N' d)
    (κ' : TensorComparison S T U V E'.forwardFunctor H'.forwardFunctor N' c') :
    c' = c + b + d + a :=
  (parity_unique E' H' κ' (κ.changeFunctors i j n)).trans (by ac_rfl)

end RMod.Classification.TensorComparison
