import RMod.Classification.Abstract.SpanIntertwiner

/-!
# Invertible generator intertwiners

The comparison and its specified inverse are computational data. The
signed intertwining law and the two inverse identities are separate
laws on these maps. The inverse's parity follows from its identities.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

variable {C D : WeaklyPointedSuperfusion.{0, 0}} {S : C.data.Obj} {T : D.data.Obj}

structure SpanIntertwinerIsoData (F G : SpanSuperfunctorData C D S T)
    extends SpanIntertwinerData F G where
  inv : G.obj (spanGenerator C S) ⟶ F.obj (spanGenerator C S)

structure SpanIntertwinerIsoLaws {F G : SpanSuperfunctorData C D S T} (a : ZMod 2)
    (d : SpanIntertwinerIsoData F G) : Prop extends SpanIntertwinerLaws a d.toSpanIntertwinerData where
  hom_inv : d.hom ≫ d.inv = 𝟙 _
  inv_hom : d.inv ≫ d.hom = 𝟙 _

structure SpanIntertwinerIso (F G : SpanSuperfunctor C D S T) (a : ZMod 2) where
  data : SpanIntertwinerIsoData F.data G.data
  laws : SpanIntertwinerIsoLaws a data

end RMod.Classification
