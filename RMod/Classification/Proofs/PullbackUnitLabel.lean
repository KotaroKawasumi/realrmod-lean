import RMod.Classification.Instances.PullbackOrbitGroup

/-!
# The selected identity-component simple is the actual tensor unit

The reference representative in type zero is normalized to its tensor
unit. Placement at the group identity therefore gives the actual model
unit, not merely its parity orbit. The induced group isomorphism also
computes the support of every selected simple's image.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C)

theorem pullbackDegreeSimple_one_object (t : Twist) :
    (pullbackDegreeSimple C hC t 1).data.object = (twistedPullback C hC t).data.tensorUnit := by
  classical
  funext k
  apply Subtype.ext
  change (if k = 1 then
    (referenceSimpleRepresentative ⟨C, hC.toPiSuperfusionLaws⟩ hC
      (Multiplicative.toAdd (t.data.rho 1))).data.object
    else (pullbackZeroObj C hC t.data k).val) =
    (if k = 1 then C.tensorUnit else (pullbackZeroObj C hC t.data k).val)
  simp only [map_one, toAdd_one, referenceSimpleRepresentative_zero]
  rfl

theorem equivalenceGaugePhi_apply (s t : Twist)
    (E : MonoidalSuperequivalence (twistedPullback C hC s).toWeaklyPointedSuperfusion
      (twistedPullback C hC t).toWeaklyPointedSuperfusion) (g : s.data.group) :
    equivalenceGaugePhi C hC s t E g =
      pullbackSimpleDegree C hC t (E.mapSimple (pullbackDegreeSimple C hC s g)) := rfl

theorem equivalenceImageUnit_degree (s t : Twist)
    (E : MonoidalSuperequivalence (twistedPullback C hC s).toWeaklyPointedSuperfusion
      (twistedPullback C hC t).toWeaklyPointedSuperfusion) :
    pullbackSimpleDegree C hC t (E.mapSimple (pullbackDegreeSimple C hC s 1)) = 1 :=
  (equivalenceGaugePhi_apply C hC s t E 1).symm.trans (map_one _)

end RMod.Classification
