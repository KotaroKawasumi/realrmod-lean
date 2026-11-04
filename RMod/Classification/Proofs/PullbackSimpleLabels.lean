import RMod.Classification.Instances.PullbackSimpleLabels

/-!
# The chosen support label is intrinsic to a simple parity orbit

Nonzero coordinates determine the label uniquely. Equal labels give a
homogeneous isomorphism by the reference property, and the selected
simple placed at g has label g.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : Twist)

theorem pullbackSimpleDegree_eq_of_simple_coordinate
    (X : SimpleObject (twistedPullback C hC t).toWeaklyPointedSuperfusion) (g : t.data.group)
    (hs : C.IsSimple (X.data.object g).val) : pullbackSimpleDegree C hC t X = g := by
  by_contra h
  exact simple_id_ne_zero hC.toWeaklyPointedSuperfusionLaws hs
    (pullbackSimpleDegree_supported C hC t X g (Ne.symm h))

theorem pullbackSimpleDegree_eq_iff
    (X Y : SimpleObject (twistedPullback C hC t).toWeaklyPointedSuperfusion) :
    pullbackSimpleDegree C hC t X = pullbackSimpleDegree C hC t Y ↔
      SameParityOrbit (twistedPullback C hC t).data.toWeaklyPointedSuperfusionData
        X.data.object Y.data.object :=
  (pullback_sameOrbit_iff_support_eq C hC t.data t.laws X.data.object Y.data.object _ _
    (pullbackSimpleDegree_supported C hC t X) (pullbackSimpleDegree_supported C hC t Y)
    (pullbackSimpleDegree_simple C hC t X) (pullbackSimpleDegree_simple C hC t Y)).symm

theorem pullbackDegreeSimple_coordinate (g : t.data.group) :
    C.IsSimple ((pullbackDegreeSimple C hC t g).data.object g).val := by
  dsimp only [pullbackDegreeSimple, pullbackDegreeSimpleData]
  rw [placedObj_at]
  exact (referenceSimpleRepresentative ⟨C, hC.toPiSuperfusionLaws⟩ hC
    (Multiplicative.toAdd (t.data.rho g))).laws.simple

theorem pullbackSimpleDegree_placed (g : t.data.group) :
    pullbackSimpleDegree C hC t (pullbackDegreeSimple C hC t g) = g :=
  pullbackSimpleDegree_eq_of_simple_coordinate C hC t _ g (pullbackDegreeSimple_coordinate C hC t g)

end RMod.Classification
