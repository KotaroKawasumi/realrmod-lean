import RMod.Classification.Abstract.TensorComparison
import RMod.Classification.Abstract.SpanNaturalIso
import RMod.Classification.Instances.HomogeneousTensorIso

/-!
# Changing the three component functors of a binary comparison

First apply the inverse output comparison, then the original binary
comparison, then tensor the two input comparisons. Every inverse is
retained explicitly, including the Koszul sign in the tensor inverse.
-/

set_option autoImplicit false

namespace RMod.Classification.TensorComparison

variable {A C : WeaklyPointedSuperfusion.{0, 0}}
  {S T : SimpleObject A} {U V : SimpleObject C}
  {E E' : SpanSuperfunctorData A C S.data.object U.data.object}
  {H H' : SpanSuperfunctorData A C T.data.object V.data.object}
  {N N' : SpanSuperfunctorData A C (simpleTensorRepresentative A S T).data.object
    (simpleTensorRepresentative C U V).data.object}

def changeFunctorsData (κ : TensorComparisonData S T U V E H N)
    (a b : ZMod 2) (i : SpanHomogeneousNatIsoData E E')
    (j : SpanHomogeneousNatIsoData H H') (n : SpanHomogeneousNatIsoData N N') :
    TensorComparisonData S T U V E' H' N' where
  app X Y :=
    ((⟨(n.inv.app (spanTensorObj A S T X Y)).hom, (n.app (spanTensorObj A S T X Y)).hom⟩ :
      IsoData C.data _ _).trans C.data (κ.app X Y)).trans C.data
        ((⟨(i.app X).hom, (i.inv.app X).hom⟩ : IsoData C.data _ _).homogeneousTensor C.data a b
          (⟨(j.app Y).hom, (j.inv.app Y).hom⟩ : IsoData C.data _ _))

end RMod.Classification.TensorComparison
