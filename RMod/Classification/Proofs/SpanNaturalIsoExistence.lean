import RMod.Classification.Proofs.SpanIntertwinerExistence
import RMod.Classification.Instances.SpanNaturalIsoExtension

/-!
# Actual homogeneous isomorphisms between component equivalences

Super Skolem--Noether supplies an invertible generator comparison, and
the explicit extension supplies its value and inverse on every object.
Thus any two equivalences between simple homogeneous spans admit a
homogeneous natural isomorphism in some parity.
-/

set_option autoImplicit false

namespace RMod.Classification

theorem exists_spanNaturalIso {C D : WeaklyPointedSuperfusion.{0, 0}}
    {S : C.data.Obj} {T : D.data.Obj} (hS : C.data.IsSimple S) (hT : D.data.IsSimple T)
    (E H : SpanSuperequivalence C D S T) :
    ∃ a : ZMod 2, Nonempty (SpanHomogeneousNatIso E.forwardFunctor H.forwardFunctor a) := by
  obtain ⟨a, ⟨t⟩⟩ := exists_spanIntertwinerIso hS hT E H
  exact ⟨a, ⟨spanNaturalIsoExtension t⟩⟩

end RMod.Classification
