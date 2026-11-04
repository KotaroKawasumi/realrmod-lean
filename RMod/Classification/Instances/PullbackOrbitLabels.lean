import RMod.Classification.Proofs.PullbackSimpleLabels

/-!
# The actual equivalence between pullback simple orbits and group labels

The forward map reads the simple's unique support. The inverse places
the selected reference simple at that support. Their inverse laws use
the reference property's characterization of homogeneous isomorphism.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : Twist)

noncomputable def pullbackOrbitDegree :
    SimpleOrbit (twistedPullback C hC t).toWeaklyPointedSuperfusion → t.data.group :=
  Quotient.lift (pullbackSimpleDegree C hC t)
    (fun X Y h => (pullbackSimpleDegree_eq_iff C hC t X Y).mpr h)

noncomputable def pullbackOrbitEquiv :
    SimpleOrbit (twistedPullback C hC t).toWeaklyPointedSuperfusion ≃ t.data.group where
  toFun := pullbackOrbitDegree C hC t
  invFun g := simpleOrbitMk _ (pullbackDegreeSimple C hC t g)
  left_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro X
    apply Quotient.sound
    apply (pullbackSimpleDegree_eq_iff C hC t _ X).mp
    exact pullbackSimpleDegree_placed C hC t _
  right_inv := pullbackSimpleDegree_placed C hC t

end RMod.Classification
