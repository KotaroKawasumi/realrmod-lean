import RMod.Classification.Proofs.PullbackOrbitType

/-!
# An equivalence compares reference generators in the same parity orbit

The type of a source simple and its image is invariant. Evaluation at
their respective supports identifies those types with the two reference
coordinates. Property P therefore identifies the reference generators
by a homogeneous isomorphism, with no chosen coefficient coordinates.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (s t : Twist)
  (E : MonoidalSuperequivalence (twistedPullback C hC s).toWeaklyPointedSuperfusion
    (twistedPullback C hC t).toWeaklyPointedSuperfusion)
  (S : SimpleObject (twistedPullback C hC s).toWeaklyPointedSuperfusion)

theorem equivalenceComponent_type_eq :
    Multiplicative.toAdd (t.data.rho (pullbackSimpleDegree C hC t (E.mapSimple S))) =
      Multiplicative.toAdd (s.data.rho (pullbackSimpleDegree C hC s S)) :=
  (pullbackSimple_type C hC t (E.mapSimple S)).symm.trans
    ((simpleType_map_equivalence (twistedPullback C hC s) (twistedPullback C hC t) E S).trans
      (pullbackSimple_type C hC s S))

theorem equivalenceComponentGenerators_sameOrbit :
    SameParityOrbit C.toWeaklyPointedSuperfusionData
      (S.data.object (pullbackSimpleDegree C hC s S)).val
      ((E.mapSimple S).data.object (pullbackSimpleDegree C hC t (E.mapSimple S))).val := by
  have hS := pullbackSimpleDegree_simple C hC s S
  have hT := pullbackSimpleDegree_simple C hC t (E.mapSimple S)
  have hrS := (InComponent.simple_iff hC hS _).mp
    (S.data.object (pullbackSimpleDegree C hC s S)).property
  have hrT := (InComponent.simple_iff hC hT _).mp
    ((E.mapSimple S).data.object (pullbackSimpleDegree C hC t (E.mapSimple S))).property
  -- Keep the ambient object fixed while changing its type label: the
  -- coordinate's subtype certificate itself depends on the old label.
  let Y : C.Obj :=
    ((E.mapSimple S).data.object (pullbackSimpleDegree C hC t (E.mapSimple S))).val
  have hrT' := Eq.mp (congrArg (fun r : ZMod 8 =>
    HasBWType C.toWeaklyPointedSuperfusionData Y r)
    (equivalenceComponent_type_eq C hC s t E S)) hrT
  exact (hC.type_detects_orbit _ _ _ hS hT hrS).mp hrT'

end RMod.Classification
