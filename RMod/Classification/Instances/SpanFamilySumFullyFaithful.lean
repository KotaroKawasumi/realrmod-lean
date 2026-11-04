import RMod.Classification.Proofs.SpanFamilySumPreimage
import Mathlib.CategoryTheory.Functor.FullyFaithful

/-!
# The finite sum functor is fully faithful on distinct simple components

Mathlib's bundle is populated with the explicit diagonal preimage and
its two proved inverse identities. No additional choice of inverse maps
is needed at this step.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

noncomputable def spanFamilySumFullyFaithful (C : WeaklyPointedSuperfusion.{0, 0})
    {I : Type} [Fintype I] (S : I → C.data.Obj) (hS : ∀ i, C.data.IsSimple (S i))
    (hST : ∀ i j, i ≠ j → ¬ SameParityOrbit C.data (S i) (S j)) : (spanFamilySum C S).FullyFaithful where
  preimage := spanFamilySumPreimage C S
  map_preimage := spanFamilySum_map_preimage C S hS hST
  preimage_map := spanFamilySum_preimage_map C S

end RMod.Classification
