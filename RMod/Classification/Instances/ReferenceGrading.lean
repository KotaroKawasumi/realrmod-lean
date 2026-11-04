import RMod.Classification.Proofs.ReferenceGrading

/-!
# A reference identifies its intrinsic group with the Brauer–Wall group

Mathlib constructs the inverse of the bijective type homomorphism. The
result retains the actual intrinsic group of simple classes as its domain.
-/

set_option autoImplicit false

namespace RMod.Classification

noncomputable def referenceGradingEquiv (C : PiSuperfusion.{0, 0})
    (hC : ReferenceProperty C.data) :
    simpleOrbitFiniteGroup C.toWeaklyPointedSuperfusion ≃* Multiplicative (ZMod 8) :=
  MulEquiv.ofBijective (intrinsicRho C) (hC.intrinsicRho_bijective C)

end RMod.Classification
