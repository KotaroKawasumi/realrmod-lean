import RMod.Classification.Proofs.SpanNaturalIsoExtension

/-!
# The completed invertible natural extension

Bundle the signed matrix component maps with their proved naturality,
degrees and inverse identities. This is an actual isomorphism of
component functors, not just agreement of their type labels.
-/

set_option autoImplicit false

namespace RMod.Classification

variable {C D : WeaklyPointedSuperfusion.{0, 0}} {S : C.data.Obj} {T : D.data.Obj}
  {F G : SpanSuperfunctor C D S T} {a : ZMod 2}

noncomputable def spanNaturalIsoExtension (t : SpanIntertwinerIso F G a) :
    SpanHomogeneousNatIso F G a :=
  ⟨spanNaturalIsoExtensionData F.data G.data a t.data, spanNaturalIsoExtensionLaws t⟩

end RMod.Classification
