import RMod.Classification.Proofs.SpanNaturalIsoExistence
import RMod.Classification.Proofs.SpanNaturalLines

/-!
# A unique parity of invertible component comparisons

Existence comes from the actual Skolem--Noether and matrix-extension
construction. The odd endomorphism vanishing theorem makes its parity
unique, and the scalar-line theorem identifies each comparison once
one invertible comparison has been chosen.
-/

set_option autoImplicit false

namespace RMod.Classification

theorem exists_unique_spanNaturalIso_parity {C D : WeaklyPointedSuperfusion.{0, 0}}
    {S : C.data.Obj} {T : D.data.Obj} (hS : C.data.IsSimple S) (hT : D.data.IsSimple T)
    (E H : SpanSuperequivalence C D S T) :
    ∃! a : ZMod 2, Nonempty (SpanHomogeneousNatIso E.forwardFunctor H.forwardFunctor a) := by
  obtain ⟨a, ⟨η⟩⟩ := exists_spanNaturalIso hS hT E H
  refine ⟨a, ⟨η⟩, ?_⟩
  rintro b ⟨θ⟩
  exact SpanHomogeneousNatIso.parity_unique E.fullyFaithful E.map_grade_iff hS θ η

end RMod.Classification
