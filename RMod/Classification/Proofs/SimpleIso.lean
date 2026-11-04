import RMod.Classification.Proofs.EvenSimple
import RMod.Classification.Instances.EvenIsos

/-!
# Transport of raw simplicity through an even isomorphism

The frozen predicate agrees with Mathlib simplicity in the even category.
Mathlib's isomorphism invariance therefore applies to the specified raw
maps and inverse, without a separate proof by monomorphism manipulation.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification

theorem simple_of_evenIso (C : WeaklyPointedSuperfusion.{u, v}) {X Y : C.data.Obj}
    (d : IsoData C.data X Y) (hd : EvenIsoLaws C.data d) (hX : C.data.IsSimple X) :
    C.data.IsSimple Y := by
  rw [isSimple_iff_evenSimple] at hX ⊢
  letI := hX
  exact CategoryTheory.Simple.of_iso (d.toEvenIso C hd).symm

end RMod.Classification
