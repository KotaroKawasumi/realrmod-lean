import RMod.Classification.Proofs.SimpleOrbitInverse
import RMod.Classification.Proofs.SimpleTensorAssociativity
import RMod.Classification.Proofs.SimpleOrbitUnit
import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.Algebra.Category.Grp.FiniteGrp

/-!
# The intrinsic finite group of simple parity classes

Multiplication is induced by tensor constituents and the identity by the
tensor unit. For an inverse we choose a representative of the quotient
and its proved weak inverse. Mathlib's right-inverse group constructor
derives all remaining group laws from the associator and unit proofs.
The external `Group` and `FiniteGrp` structures are reused directly.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : WeaklyPointedSuperfusion.{0, 0})

noncomputable def simpleOrbitInv (x : SimpleOrbit C) : SimpleOrbit C :=
  simpleOrbitMk C (exists_simple_right_inverse C (Quotient.out x)).choose

theorem simpleOrbitMul_inv (x : SimpleOrbit C) :
    simpleOrbitMul C x (simpleOrbitInv C x) = unitOrbit C := by
  have h := (exists_simple_right_inverse C (Quotient.out x)).choose_spec
  change simpleOrbitMul C (Quotient.mk _ (Quotient.out x)) (simpleOrbitInv C x) = unitOrbit C at h
  rwa [Quotient.out_eq] at h

noncomputable instance simpleOrbit_group : Group (SimpleOrbit C) :=
  letI : Mul (SimpleOrbit C) := ⟨simpleOrbitMul C⟩
  letI : One (SimpleOrbit C) := ⟨unitOrbit C⟩
  letI : Inv (SimpleOrbit C) := ⟨simpleOrbitInv C⟩
  Group.ofRightAxioms (simpleOrbitMul_assoc C) (simpleOrbitMul_unit C) (simpleOrbitMul_inv C)

noncomputable def simpleOrbitFiniteGroup : FiniteGrp := FiniteGrp.of (SimpleOrbit C)

end RMod.Classification
