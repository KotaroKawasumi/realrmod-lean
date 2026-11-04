import RMod.BrundanEllis.StackingReferenceBinaryDeletion
import RMod.BrundanEllis.StackingReferenceShuffleUnit

/-! Both actual unit routes of the binary comparison, including the two original parity factors and their ordered deletions. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

namespace RMod.BrundanEllis.Stacking
open RMod.Classification
local notation "R" => reference.data.toWeaklyPointedSuperfusionData
local notation "hR" => referenceProperty.toWeaklyPointedSuperfusionLaws
local notation "P" => reference.data.pi
local notation "I" => reference.data.tensorUnit

/-- The even binary comparison, including its two output parity factors,
respects the left unit route. All unit reference crossings have already
been verified without additional hexagon hypotheses. -/
theorem referenceBinaryBlock_leftUnit (a : ZMod 8) (X Y : (R).Obj)
    (hX : InComponent R a X) :
    (R).comp
      (referenceBinaryBlockData 0 a I I X Y (InComponent.tensor_unit referenceProperty) hX 0 0).hom
      ((R).tensorHom
        ((R).comp ((P).rightFactorDeletion ((R).tensorObj I X) 0).hom ((R).leftUnitorHom X))
        ((R).comp ((P).rightFactorDeletion ((R).tensorObj I Y) 0).hom ((R).leftUnitorHom Y))) =
    (R).comp
      ((P).rightFactorDeletion ((R).tensorObj ((R).tensorObj I I) ((R).tensorObj X Y))
        (0 + 0 + ReferenceCommutor.degree 0 a)).hom
      ((R).comp
        ((R).tensorHom ((R).leftUnitorHom I) ((R).id ((R).tensorObj X Y)))
        ((R).leftUnitorHom ((R).tensorObj X Y))) := by
  rw [← interchange_second_even hR _ _ _ _ ((hR).left_unitor_hom_even Y),
    ← (hR).comp_assoc, referenceBinaryBlock_deletion]
  simp only [mul_zero, ZMod.val_zero, pow_zero, (hR).one_smul, (hR).comp_assoc]
  rw [referenceShuffle_leftUnit]

/-- The analogous right unit route, retaining the actual target parity
deletions so that it can be inserted into convolution comparisons. -/
theorem referenceBinaryBlock_rightUnit (a : ZMod 8) (X Y : (R).Obj)
    (hY : InComponent R a Y) :
    (R).comp
      (referenceBinaryBlockData a 0 X Y I I hY (InComponent.tensor_unit referenceProperty) 0 0).hom
      ((R).tensorHom
        ((R).comp ((P).rightFactorDeletion ((R).tensorObj X I) 0).hom ((R).rightUnitorHom X))
        ((R).comp ((P).rightFactorDeletion ((R).tensorObj Y I) 0).hom ((R).rightUnitorHom Y))) =
    (R).comp
      ((P).rightFactorDeletion ((R).tensorObj ((R).tensorObj X Y) ((R).tensorObj I I))
        (0 + 0 + ReferenceCommutor.degree a 0)).hom
      ((R).comp
        ((R).tensorHom ((R).id ((R).tensorObj X Y)) ((R).leftUnitorHom I))
        ((R).rightUnitorHom ((R).tensorObj X Y))) := by
  rw [← interchange_second_even hR _ _ _ _ ((hR).right_unitor_hom_even Y),
    ← (hR).comp_assoc, referenceBinaryBlock_deletion]
  simp only [mul_zero, ZMod.val_zero, pow_zero, (hR).one_smul, (hR).comp_assoc]
  rw [referenceShuffle_rightUnit]

end RMod.BrundanEllis.Stacking
