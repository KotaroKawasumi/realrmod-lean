import RMod.Classification.Proofs.EquivalenceSimpleOrbits

/-! # The induced Mathlib isomorphism of intrinsic orbit groups -/

set_option autoImplicit false

namespace RMod.Classification.MonoidalSuperequivalence

variable {C D : WeaklyPointedSuperfusion.{0, 0}}

def simpleOrbitMulEquiv (E : MonoidalSuperequivalence C D) : SimpleOrbit C ≃* SimpleOrbit D where
  toEquiv := E.simpleOrbitEquiv
  map_mul' := E.simpleOrbitMap_mul

end RMod.Classification.MonoidalSuperequivalence
