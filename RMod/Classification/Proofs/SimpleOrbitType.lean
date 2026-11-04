import RMod.Classification.Instances.SimpleOrbitType
import RMod.Classification.Proofs.TensorTypes

/-!
# Additivity of the label on the intrinsic finite group

The endomorphism algebra of a tensor product has the sum of the two
Brauer–Wall labels. Its homogeneous sum presentation identifies this
with the label of the chosen tensor constituent. Quotient induction
therefore proves additivity on all simple classes, and the unit equation
forces the unit label to vanish.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusion.{0, 0})

attribute [local implicit_reducible] PiSuperfusion.toWeaklyPointedSuperfusion

theorem simpleTensorRepresentative_type (X Y : SimpleObject C.toWeaklyPointedSuperfusion) :
    simpleType C (simpleTensorRepresentative C.toWeaklyPointedSuperfusion X Y) =
      simpleType C X + simpleType C Y := by
  let D := C.toWeaklyPointedSuperfusion
  let R := simpleTensorRepresentative D X Y
  let d := simpleDecomposition D (D.data.tensorObj X.data.object Y.data.object)
  have hn := d.size_pos (tensor_id_ne_zero (C := D)
    (simple_id_ne_zero D.laws X.laws.simple) (simple_id_ne_zero D.laws Y.laws.simple))
  obtain ⟨b⟩ := tensorRepresentative_homogeneousSum D X Y
  have hprod := tensorEnd_isBWEquivalent_realRep D X.data.object Y.data.object Y.laws.simple
    (simpleType_spec C X) (simpleType_spec C Y)
  have hconst := (b.isBWEquivalent (C := D) hn).trans
    (HasBWType.end_isBWEquivalent_realRep D (simpleType_spec C R))
  exact (realRep_label_eq_of_isBWEquivalent (hprod.symm.trans hconst)).symm

theorem simpleOrbitType_mul (x y : SimpleOrbit C.toWeaklyPointedSuperfusion) :
    simpleOrbitType C (x * y) = simpleOrbitType C x + simpleOrbitType C y := by
  refine Quotient.inductionOn₂ x y ?_
  intro X Y
  exact simpleTensorRepresentative_type C X Y

theorem simpleOrbitType_one : simpleOrbitType C 1 = 0 := by
  have h := simpleOrbitType_mul C 1 1
  rw [one_mul] at h
  exact (add_left_cancel ((add_zero _).trans h)).symm

end RMod.Classification
