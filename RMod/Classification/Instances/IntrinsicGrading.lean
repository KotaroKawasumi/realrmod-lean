import RMod.Classification.Proofs.SimpleOrbitType

/-!
# The group homomorphism used by reconstruction

The finite group is the intrinsic group of simple parity classes, and
its homomorphism to the order-eight Brauer–Wall group is the proved
additive type map. Mathlib supplies the group and homomorphism bundles.
-/

set_option autoImplicit false

namespace RMod.Classification

noncomputable def intrinsicRho (C : PiSuperfusion.{0, 0}) :
    simpleOrbitFiniteGroup C.toWeaklyPointedSuperfusion →* Multiplicative (ZMod 8) where
  toFun x := Multiplicative.ofAdd (simpleOrbitType C x)
  map_one' := simpleOrbitType_one C
  map_mul' x y := simpleOrbitType_mul C x y

end RMod.Classification
