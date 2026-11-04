import RMod.Classification.Instances.SimpleOrbitRepresentatives
import RMod.Classification.Instances.SimpleOrbitType

/-!
# Types and products of the normalized simple representatives

The representative has precisely the type of its quotient class. The
simple representative of its tensor product lies in the chosen product
class, allowing component functors to use fixed group-indexed spans.
-/

set_option autoImplicit false

namespace RMod.Classification

theorem simpleOrbitRepresentative_type (C : PiSuperfusion.{0, 0})
    (g : SimpleOrbit C.toWeaklyPointedSuperfusion) :
    HasBWType C.data.toWeaklyPointedSuperfusionData
      (simpleOrbitRepresentative C.toWeaklyPointedSuperfusion g).data.object (simpleOrbitType C g) := by
  have he : simpleType C (simpleOrbitRepresentative C.toWeaklyPointedSuperfusion g) = simpleOrbitType C g :=
    congrArg (simpleOrbitType C) (simpleOrbitRepresentative_class C.toWeaklyPointedSuperfusion g)
  have hs := simpleType_spec C (simpleOrbitRepresentative C.toWeaklyPointedSuperfusion g)
  rw [he] at hs
  exact hs

theorem simpleOrbitRepresentative_mul (C : WeaklyPointedSuperfusion.{0, 0}) (g h : SimpleOrbit C) :
    SameParityOrbit C.data
      (simpleTensorRepresentative C (simpleOrbitRepresentative C g) (simpleOrbitRepresentative C h)).data.object
      (simpleOrbitRepresentative C (g * h)).data.object := by
  apply @Quotient.exact _ (simpleOrbitSetoid C)
    (simpleTensorRepresentative C (simpleOrbitRepresentative C g) (simpleOrbitRepresentative C h))
    (simpleOrbitRepresentative C (g * h))
  change simpleOrbitMul C (simpleOrbitMk C (simpleOrbitRepresentative C g))
    (simpleOrbitMk C (simpleOrbitRepresentative C h)) = simpleOrbitMk C (simpleOrbitRepresentative C (g * h))
  rw [simpleOrbitRepresentative_class, simpleOrbitRepresentative_class, simpleOrbitRepresentative_class]
  rfl

end RMod.Classification
