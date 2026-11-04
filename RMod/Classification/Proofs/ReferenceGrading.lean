import RMod.Classification.Instances.IntrinsicGrading

/-!
# The intrinsic type map is bijective precisely for a reference

The reference hypotheses realize every type and identify simples of the
same type up to homogeneous isomorphism. On the intrinsic quotient these
are exactly surjectivity and injectivity of the proved group homomorphism.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusion.{0, 0}) (hC : ReferenceProperty C.data)

include hC

theorem ReferenceProperty.intrinsicRho_bijective : Function.Bijective (intrinsicRho C) := by
  constructor
  · intro x y
    refine Quotient.inductionOn₂ x y ?_
    intro X Y h
    have he : simpleType C X = simpleType C Y := congrArg Multiplicative.toAdd h
    apply Quotient.sound
    apply (hC.type_detects_orbit X.data.object Y.data.object (simpleType C X)
      X.laws.simple Y.laws.simple (simpleType_spec C X)).mp
    rw [he]
    exact simpleType_spec C Y
  · intro r
    obtain ⟨X, hX, hr⟩ := hC.realizes_type (Multiplicative.toAdd r)
    let S : SimpleObject C.toWeaklyPointedSuperfusion := ⟨⟨X⟩, ⟨hX⟩⟩
    refine ⟨simpleOrbitMk C.toWeaklyPointedSuperfusion S, ?_⟩
    change simpleType C S = Multiplicative.toAdd r
    exact HasBWType.unique C.toWeaklyPointedSuperfusion (simpleType_spec C S) hr

end RMod.Classification
