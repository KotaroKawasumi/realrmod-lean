import RMod.Classification.Abstract.SimpleObjects
import RMod.Classification.Proofs.Grading

/-!
# The intrinsic quotient of simple objects by homogeneous isomorphism

Mathlib's setoid and quotient retain the actual parity-orbit relation.
The unit gives a distinguished class. Multiplication and its group laws
will be obtained from tensor constituents, rather than from type labels.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : WeaklyPointedSuperfusion.{0, 0})

def simpleOrbitSetoid : Setoid (SimpleObject C) where
  r X Y := SameParityOrbit C.data X.data.object Y.data.object
  iseqv := ⟨fun X => SameParityOrbit.refl C.laws X.data.object,
    fun h => SameParityOrbit.symm h, fun h k => SameParityOrbit.trans C.laws h k⟩

def SimpleOrbit : Type := Quotient (simpleOrbitSetoid C)

def simpleOrbitMk (X : SimpleObject C) : SimpleOrbit C := Quotient.mk _ X

def unitSimpleData : SimpleObjectData C.data := ⟨C.data.tensorUnit⟩

theorem unitSimpleLaws : SimpleObjectLaws C.data (unitSimpleData C) := ⟨C.laws.simple_unit⟩

def unitSimple : SimpleObject C := ⟨unitSimpleData C, unitSimpleLaws C⟩

def unitOrbit : SimpleOrbit C := simpleOrbitMk C (unitSimple C)

end RMod.Classification
