import RMod.Classification.Instances.PullbackSupportedEnd
import RMod.Classification.Instances.PullbackOrbitGroup
import RMod.Classification.Proofs.EndTypeInvariance
import RMod.Classification.Proofs.EquivalenceOrbitType

/-!
# The intrinsic type on a pullback model is its given rho

Evaluation at a simple's unique support is an actual graded algebra
isomorphism on endomorphisms. Its coordinate lies in the prescribed
reference type, so type uniqueness identifies the intrinsic label.
Consequently an arbitrary monoidal equivalence induces a group
relabeling compatible with the two supplied type homomorphisms.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : Twist)

theorem pullbackSimple_type
    (X : SimpleObject (twistedPullback C hC t).toWeaklyPointedSuperfusion) :
    simpleType (twistedPullback C hC t) X =
      Multiplicative.toAdd (t.data.rho (pullbackSimpleDegree C hC t X)) :=
  HasBWType.label_eq_of_endEquiv (twistedPullback C hC t).toWeaklyPointedSuperfusion
    ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩
    (simpleType_spec (twistedPullback C hC t) X)
    ((InComponent.simple_iff hC (pullbackSimpleDegree_simple C hC t X) _).mp
      (X.data.object (pullbackSimpleDegree C hC t X)).property)
    (pullbackSupportedEndEquiv C hC t X.data.object (pullbackSimpleDegree C hC t X)
      (pullbackSimpleDegree_supported C hC t X))

theorem pullback_intrinsicRho
    (g : SimpleOrbit (twistedPullback C hC t).toWeaklyPointedSuperfusion) :
    intrinsicRho (twistedPullback C hC t) g = t.data.rho (pullbackOrbitMulEquiv C hC t g) := by
  refine Quotient.inductionOn g ?_
  intro X
  exact congrArg Multiplicative.ofAdd (pullbackSimple_type C hC t X)

omit t in
theorem equivalenceGaugePhi_rho (s t : Twist)
    (E : MonoidalSuperequivalence (twistedPullback C hC s).toWeaklyPointedSuperfusion
      (twistedPullback C hC t).toWeaklyPointedSuperfusion) (g : s.data.group) :
    t.data.rho (equivalenceGaugePhi C hC s t E g) = s.data.rho g := by
  let q := (pullbackOrbitMulEquiv C hC s).symm g
  calc
    t.data.rho (equivalenceGaugePhi C hC s t E g) =
        intrinsicRho (twistedPullback C hC t) (E.simpleOrbitMulEquiv q) :=
      (pullback_intrinsicRho C hC t (E.simpleOrbitMulEquiv q)).symm
    _ = intrinsicRho (twistedPullback C hC s) q :=
      intrinsicRho_map_equivalence (twistedPullback C hC s) (twistedPullback C hC t) E q
    _ = s.data.rho (pullbackOrbitMulEquiv C hC s q) := pullback_intrinsicRho C hC s q
    _ = s.data.rho g := congrArg s.data.rho ((pullbackOrbitMulEquiv C hC s).apply_symm_apply g)

end RMod.Classification
