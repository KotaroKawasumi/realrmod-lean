import RMod.Classification.Instances.EquivalenceOrbitGroup
import RMod.Classification.Instances.IntrinsicGrading

/-!
# The induced orbit group isomorphism preserves the intrinsic type map

The specified real graded equivalence preserves Clifford amplifications
of endomorphism algebras. Uniqueness of a simple object's intrinsic type
therefore identifies the labels before and after mapping the object.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C D : PiSuperfusion.{0, 0})
  (E : MonoidalSuperequivalence C.toWeaklyPointedSuperfusion D.toWeaklyPointedSuperfusion)

theorem simpleType_map_equivalence (X : SimpleObject C.toWeaklyPointedSuperfusion) :
    simpleType D (E.mapSimple X) = simpleType C X :=
  HasBWType.unique D.toWeaklyPointedSuperfusion (simpleType_spec D (E.mapSimple X))
    (E.hasBWType_map_iff.mpr (simpleType_spec C X))

theorem simpleOrbitType_map_equivalence (g : SimpleOrbit C.toWeaklyPointedSuperfusion) :
    simpleOrbitType D (E.simpleOrbitMap g) = simpleOrbitType C g := by
  refine Quotient.inductionOn g ?_
  exact simpleType_map_equivalence C D E

theorem intrinsicRho_map_equivalence (g : SimpleOrbit C.toWeaklyPointedSuperfusion) :
    intrinsicRho D (E.simpleOrbitMulEquiv g) = intrinsicRho C g :=
  congrArg Multiplicative.ofAdd (simpleOrbitType_map_equivalence C D E g)

end RMod.Classification
