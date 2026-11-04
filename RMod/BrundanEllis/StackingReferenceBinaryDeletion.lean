import RMod.BrundanEllis.StackingReferenceTripleData
import RMod.BrundanEllis.StackingReferenceBinaryNaturality
import RMod.BrundanEllis.StackingParityRedistributionDeletion

/-! Compatibility of the actual binary comparison with deletion of the output parities and either input pair. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

namespace RMod.BrundanEllis.Stacking
open RMod.Classification
local notation "R" => reference.data.toWeaklyPointedSuperfusionData
local notation "hR" => referenceProperty.toWeaklyPointedSuperfusionLaws
local notation "P" => reference.data.pi
local notation "hP" => referenceProperty.pi

/-- The binary comparison is measured by deleting its two output parities. -/
theorem referenceBinaryBlock_deletion (b c : ZMod 8) (A B C D : (R).Obj)
    (hB : InComponent R b B) (hC : InComponent R c C) (p q : ZMod 2) :
    (R).comp (referenceBinaryBlockData b c A B C D hB hC p q).hom
      ((R).tensorHom ((P).rightFactorDeletion ((R).tensorObj A C) q).hom
        ((P).rightFactorDeletion ((R).tensorObj B D) p).hom) =
    (R).smul ((-1 : ℝ) ^ (p * q).val)
      ((R).comp ((P).rightFactorDeletion ((R).tensorObj ((R).tensorObj A B) ((R).tensorObj C D))
        (p + q + ReferenceCommutor.degree b c)).hom
        (referenceShuffleData b c A B C D hB hC).hom) :=
  parityRedistribution_deletion hR hP _ _ _ p q _ _

/-- Deleting parity factors in the first input pair commutes with the
outer binary comparison. No two nonzero middle degrees cross here. -/
theorem referenceBinaryBlock_leftDeletion (b c : ZMod 8) (A B C D : (R).Obj)
    (hB : InComponent R b B) (hC : InComponent R c C) (a d p q : ZMod 2) :
    (R).comp
      ((R).tensorHom
        ((R).tensorHom
          ((R).tensorHom ((P).rightFactorDeletion A a).hom ((P).rightFactorDeletion B d).hom)
          ((R).id ((R).tensorObj C D)))
        ((R).id ((P).factor (p + q + ReferenceCommutor.degree b c))))
      (referenceBinaryBlockData b c A B C D hB hC p q).hom =
    (R).comp
      (referenceBinaryBlockData b c ((R).tensorObj A ((P).factor a))
        ((R).tensorObj B ((P).factor d)) C D
        (by simpa only [add_zero] using hB.tensor referenceProperty (InComponent.parity_factor referenceProperty d)) hC p q).hom
      ((R).tensorHom
        ((R).tensorHom ((R).tensorHom ((P).rightFactorDeletion A a).hom ((R).id C)) ((R).id ((P).factor q)))
        ((R).tensorHom ((R).tensorHom ((P).rightFactorDeletion B d).hom ((R).id D)) ((R).id ((P).factor p)))) := by
  have hh := referenceBinaryBlock_naturality b c ((R).tensorObj A ((P).factor a)) A
    ((R).tensorObj B ((P).factor d)) B C C D D
    (by simpa only [add_zero] using hB.tensor referenceProperty (InComponent.parity_factor referenceProperty d)) hB hC hC
    ((P).rightFactorDeletion A a).hom ((P).rightFactorDeletion B d).hom ((R).id C) ((R).id D)
    a d 0 0 p q ((hP).rightFactorDeletion_homogeneousIso hR A a).hom_grade
    ((hP).rightFactorDeletion_homogeneousIso hR B d).hom_grade ((hR).id_even C) ((hR).id_even D)
  simpa only [(hR).tensor_id, mul_zero, ReferenceCommutor.paritySign_pow, ZMod.val_zero, pow_zero, (hR).one_smul] using hh

/-- The analogous naturality calculation deletes the second input pair. -/
theorem referenceBinaryBlock_rightDeletion (b c : ZMod 8) (A B C D : (R).Obj)
    (hB : InComponent R b B) (hC : InComponent R c C) (a d p q : ZMod 2) :
    (R).comp
      ((R).tensorHom
        ((R).tensorHom ((R).id ((R).tensorObj A B))
          ((R).tensorHom ((P).rightFactorDeletion C a).hom ((P).rightFactorDeletion D d).hom))
        ((R).id ((P).factor (p + q + ReferenceCommutor.degree b c))))
      (referenceBinaryBlockData b c A B C D hB hC p q).hom =
    (R).comp
      (referenceBinaryBlockData b c A B
        ((R).tensorObj C ((P).factor a)) ((R).tensorObj D ((P).factor d)) hB
        (by simpa only [add_zero] using hC.tensor referenceProperty (InComponent.parity_factor referenceProperty a)) p q).hom
      ((R).tensorHom
        ((R).tensorHom ((R).tensorHom ((R).id A) ((P).rightFactorDeletion C a).hom) ((R).id ((P).factor q)))
        ((R).tensorHom ((R).tensorHom ((R).id B) ((P).rightFactorDeletion D d).hom) ((R).id ((P).factor p)))) := by
  have hh := referenceBinaryBlock_naturality b c A A B B
    ((R).tensorObj C ((P).factor a)) C ((R).tensorObj D ((P).factor d)) D hB hB
    (by simpa only [add_zero] using hC.tensor referenceProperty (InComponent.parity_factor referenceProperty a)) hC
    ((R).id A) ((R).id B) ((P).rightFactorDeletion C a).hom ((P).rightFactorDeletion D d).hom
    0 0 a d p q ((hR).id_even A) ((hR).id_even B)
    ((hP).rightFactorDeletion_homogeneousIso hR C a).hom_grade
    ((hP).rightFactorDeletion_homogeneousIso hR D d).hom_grade
  simpa only [(hR).tensor_id, zero_mul, ReferenceCommutor.paritySign_pow, ZMod.val_zero, pow_zero, (hR).one_smul] using hh

end RMod.BrundanEllis.Stacking
