import RMod.Classification.Abstract.SpanNaturalIso
import RMod.Classification.Abstract.SpanIntertwinerIso
import RMod.Classification.Instances.SpanNaturalExtensionData

/-!
# Extending the two maps of a generator isomorphism

The forward and inverse component families use the same signed matrix
extension formula. Only the specified generator maps enter the data;
their inverse laws are proved separately for these exact families.
-/

set_option autoImplicit false

namespace RMod.Classification

variable {C D : WeaklyPointedSuperfusion.{0, 0}} {S : C.data.Obj} {T : D.data.Obj}

noncomputable def spanNaturalIsoExtensionData (F G : SpanSuperfunctorData C D S T)
    (a : ZMod 2) (t : SpanIntertwinerIsoData F G) : SpanHomogeneousNatIsoData F G :=
  ⟨spanNaturalExtensionData F G a t.toSpanIntertwinerData,
    spanNaturalExtensionData G F a ⟨t.inv⟩⟩

end RMod.Classification
