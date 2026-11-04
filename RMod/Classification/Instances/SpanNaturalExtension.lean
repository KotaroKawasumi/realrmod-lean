import RMod.Classification.Proofs.SpanNaturalExtension

/-!
# The completed extension and evaluation of generator comparisons

Extension bundles the constructed matrix components with their proved
degree and naturality. Evaluation at the generator retains the given
component and restricts its naturality law to generator endomorphisms.
-/

set_option autoImplicit false

namespace RMod.Classification

variable {C D : WeaklyPointedSuperfusion.{0, 0}} {S : C.data.Obj} {T : D.data.Obj}
  {F G : SpanSuperfunctor C D S T} {a : ZMod 2}

noncomputable def spanNaturalExtension (t : SpanIntertwiner F G a) : SpanHomogeneousNat F G a :=
  ⟨spanNaturalExtensionData F.data G.data a t.data, spanNaturalExtensionLaws t⟩

def SpanHomogeneousNat.intertwinerData (η : SpanHomogeneousNatData F.data G.data) :
    SpanIntertwinerData F.data G.data := ⟨η.app (spanGenerator C S)⟩

theorem SpanHomogeneousNat.intertwinerLaws (η : SpanHomogeneousNat F G a) :
    SpanIntertwinerLaws a (intertwinerData η.data) where
  grade := η.laws.grade _
  intertwines f hf := η.laws.naturality f hf

def SpanHomogeneousNat.toIntertwiner (η : SpanHomogeneousNat F G a) : SpanIntertwiner F G a :=
  ⟨intertwinerData η.data, intertwinerLaws η⟩

end RMod.Classification
