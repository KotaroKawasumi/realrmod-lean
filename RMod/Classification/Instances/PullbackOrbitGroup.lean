import RMod.Classification.Proofs.PullbackOrbitMultiplication
import RMod.Classification.Instances.EquivalenceOrbitGroup

/-!
# The original group recovered from a pullback model

The support equivalence respects multiplication. Composing it with the
intrinsic group isomorphism induced by an arbitrary monoidal equivalence
gives the required relabeling between the two classification groups.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C)

noncomputable def pullbackOrbitMulEquiv (t : Twist) :
    SimpleOrbit (twistedPullback C hC t).toWeaklyPointedSuperfusion ≃* t.data.group where
  toEquiv := pullbackOrbitEquiv C hC t
  map_mul' := pullbackOrbitDegree_mul C hC t

noncomputable def equivalenceGaugePhi (s t : Twist)
    (E : MonoidalSuperequivalence (twistedPullback C hC s).toWeaklyPointedSuperfusion
      (twistedPullback C hC t).toWeaklyPointedSuperfusion) : s.data.group ≃* t.data.group :=
  (pullbackOrbitMulEquiv C hC s).symm.trans
    (E.simpleOrbitMulEquiv.trans (pullbackOrbitMulEquiv C hC t))

end RMod.Classification
