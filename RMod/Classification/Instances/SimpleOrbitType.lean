import RMod.Classification.Instances.SimpleOrbitGroup
import RMod.Classification.Proofs.IntrinsicTypes

/-!
# The intrinsic Brauer–Wall label on simple parity classes

Each simple has a unique intrinsic Clifford type. Homogeneous isomorphism
preserves this type, so the selected label descends to the actual simple
orbit quotient. No injectivity of this map is assumed: many different
simple classes may have the same Brauer–Wall label.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusion.{0, 0})

noncomputable def simpleType (X : SimpleObject C.toWeaklyPointedSuperfusion) : ZMod 8 :=
  (simple_has_unique_type C X.data.object X.laws.simple).exists.choose

theorem simpleType_spec (X : SimpleObject C.toWeaklyPointedSuperfusion) :
    HasBWType C.data.toWeaklyPointedSuperfusionData X.data.object (simpleType C X) :=
  (simple_has_unique_type C X.data.object X.laws.simple).exists.choose_spec

theorem simpleType_congr (X Y : SimpleObject C.toWeaklyPointedSuperfusion)
    (h : SameParityOrbit C.data.toWeaklyPointedSuperfusionData X.data.object Y.data.object) :
    simpleType C X = simpleType C Y :=
  HasBWType.unique C.toWeaklyPointedSuperfusion
    ((SameParityOrbit.hasBWType_iff C.laws.toWeaklyPointedSuperfusionLaws h _).mp (simpleType_spec C X))
    (simpleType_spec C Y)

noncomputable def simpleOrbitType : SimpleOrbit C.toWeaklyPointedSuperfusion → ZMod 8 :=
  Quotient.lift (simpleType C) (simpleType_congr C)

theorem simpleOrbitType_mk (X : SimpleObject C.toWeaklyPointedSuperfusion) :
    simpleOrbitType C (simpleOrbitMk C.toWeaklyPointedSuperfusion X) = simpleType C X := rfl

end RMod.Classification
