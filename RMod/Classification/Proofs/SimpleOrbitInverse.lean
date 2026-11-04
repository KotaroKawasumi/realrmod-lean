import RMod.Classification.Proofs.SimpleOfSchur
import RMod.Classification.Instances.SimpleOrbitMultiplication

/-!
# Right inverses of the intrinsic simple classes

Weak pointedness provides a dual whose product is a nonempty homogeneous
sum of units. Dual simplicity makes this a valid simple representative.
A nonzero unit inclusion identifies its product class with the unit.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : WeaklyPointedSuperfusion.{0, 0})

theorem exists_simple_right_inverse (X : SimpleObject C) :
    ∃ Y : SimpleObject C,
      simpleOrbitMul C (simpleOrbitMk C X) (simpleOrbitMk C Y) = unitOrbit C := by
  obtain ⟨Y, hXY, p, q, hpq, i, pr, hi, _, hd, _, _⟩ :=
    C.laws.weakly_pointed X.data.object X.laws.simple
  obtain ⟨pair⟩ := (hasExactPairing_iff C _ _).mp hXY
  let Y' : SimpleObject C := ⟨⟨Y⟩, ⟨pair.right_simple X.laws.simple⟩⟩
  refine ⟨Y', Quotient.sound (SameParityOrbit.symm ?_)⟩
  have hn : Nonempty (Fin p ⊕ Fin q) := by
    by_cases hp : 0 < p
    · exact ⟨Sum.inl ⟨0, hp⟩⟩
    · exact ⟨Sum.inr ⟨0, by omega⟩⟩
  obtain ⟨k⟩ := hn
  apply simple_orbit_of_map_to_tensor C X Y' C.laws.simple_unit (i k) (hi k)
  intro hz
  have h := hd k
  rw [hz, raw_zero_comp C.laws] at h
  exact simple_id_ne_zero C.laws C.laws.simple_unit h.symm

end RMod.Classification
