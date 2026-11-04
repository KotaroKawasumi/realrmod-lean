import RMod.Classification.Proofs.SimpleTensorCongruence
import RMod.Classification.Proofs.SimpleOrbits

/-!
# Multiplication of simple parity classes

The product is the class of any simple constituent of the tensor product.
The congruence theorem makes this a map on Mathlib quotients; the chosen
decomposition is used only to supply an actual representative.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : WeaklyPointedSuperfusion.{0, 0})

noncomputable def simpleOrbitMul : SimpleOrbit C → SimpleOrbit C → SimpleOrbit C :=
  Quotient.map₂ (sa := simpleOrbitSetoid C) (sb := simpleOrbitSetoid C) (sc := simpleOrbitSetoid C)
    (simpleTensorRepresentative C) (fun {X X'} hX {Y Y'} hY =>
      simpleTensorRepresentative_congr C X X' Y Y' hX hY)

theorem simpleOrbitMul_mk (X Y : SimpleObject C) :
    simpleOrbitMul C (simpleOrbitMk C X) (simpleOrbitMk C Y) =
      simpleOrbitMk C (simpleTensorRepresentative C X Y) := rfl

end RMod.Classification
