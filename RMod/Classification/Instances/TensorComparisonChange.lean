import RMod.Classification.Proofs.TensorComparisonChange

/-! # A completed binary comparison after changing component functors -/

set_option autoImplicit false

namespace RMod.Classification.TensorComparison

def changeFunctors {A C : WeaklyPointedSuperfusion.{0, 0}}
    {S T : SimpleObject A} {U V : SimpleObject C}
    {E E' : SpanSuperfunctor A C S.data.object U.data.object}
    {H H' : SpanSuperfunctor A C T.data.object V.data.object}
    {N N' : SpanSuperfunctor A C (simpleTensorRepresentative A S T).data.object
      (simpleTensorRepresentative C U V).data.object}
    {a b c d : ZMod 2} (κ : TensorComparison S T U V E H N c)
    (i : SpanHomogeneousNatIso E E' a) (j : SpanHomogeneousNatIso H H' b)
    (n : SpanHomogeneousNatIso N N' d) :
    TensorComparison S T U V E' H' N' ((d + c) + (a + b)) :=
  ⟨changeFunctorsData κ.data a b i.data j.data n.data, changeFunctorsLaws κ i j n⟩

end RMod.Classification.TensorComparison
