import RMod.Classification.Instances.SimpleOrbits

/-!
# Finiteness and equality of intrinsic simple parity classes

Quotient equality is exactly homogeneous isomorphism, and the supplied
finite simple representatives surject onto the quotient. Mathlib's
`Finite` interface expresses this finiteness; no new finite-group
structure or enumeration is added to the public statement.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : WeaklyPointedSuperfusion.{0, 0})

theorem simpleOrbitMk_eq_iff (X Y : SimpleObject C) :
    simpleOrbitMk C X = simpleOrbitMk C Y ↔ SameParityOrbit C.data X.data.object Y.data.object :=
  ⟨Quotient.exact, fun h => @Quotient.sound _ (simpleOrbitSetoid C) X Y h⟩

instance simpleOrbit_finite : Finite (SimpleOrbit C) := by
  classical
  obtain ⟨n, S, hS, h⟩ := C.laws.finite_simple_representatives
  let f : Fin n → SimpleOrbit C := fun i => simpleOrbitMk C ⟨⟨S i⟩, ⟨hS i⟩⟩
  apply Finite.of_surjective f
  intro a
  refine Quotient.inductionOn a ?_
  intro X
  obtain ⟨i, p, hi⟩ := h X.data.object X.laws.simple
  exact ⟨i, Quotient.sound (SameParityOrbit.symm ⟨p, hi⟩)⟩

instance simpleOrbit_nonempty : Nonempty (SimpleOrbit C) := ⟨unitOrbit C⟩

end RMod.Classification
