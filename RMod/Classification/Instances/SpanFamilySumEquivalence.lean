import RMod.Classification.Instances.SpanFamilySumFullyFaithful
import RMod.Classification.Instances.SpanFamilySumPreimages
import RMod.Classification.Instances.SpanFamilyInverse

/-!
# Realization of a complete set of simple components

Orthogonality supplies explicit inverse Hom maps. Grouping simple
summands supplies actual even object preimages. Together they produce an
ordinary equivalence retaining the chosen inverse functor and counit.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

noncomputable def spanFamilySumEquivalence (C : WeaklyPointedSuperfusion.{0, 0})
    {I : Type} [Fintype I] (S : I → C.data.Obj) (hS : ∀ i, C.data.IsSimple (S i))
    (hST : ∀ i j, i ≠ j → ¬ SameParityOrbit C.data (S i) (S j))
    (cover : ∀ T, C.data.IsSimple T → ∃ i, SameParityOrbit C.data (S i) T) :
    SpanFamilyCategory C S ≌ LinearCategory C :=
  (spanFamilySumPreimages C S hS cover).underlyingEquivalence (spanFamilySumFullyFaithful C S hS hST)

end RMod.Classification
