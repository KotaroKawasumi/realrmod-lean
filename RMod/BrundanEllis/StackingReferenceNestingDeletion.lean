import RMod.BrundanEllis.StackingReferenceBinaryDeletion
import RMod.BrundanEllis.StackingDoubleDeletion
import RMod.BrundanEllis.StackingOrderedDeletionTensor

/-! Compute the full parity-deletion sign of both binary nestings before evaluating the original local associators. -/

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

/-- Delete the parity factors in the left binary nesting. The three
parity-interchange signs and the crossing of the outer deletion with the
first shuffle are retained explicitly. -/
theorem referenceLeftNesting_deletion (b c d e : ZMod 8) (A B C D E F : (R).Obj)
    (hB : InComponent R b B) (hC : InComponent R c C)
    (hD : InComponent R d D) (hE : InComponent R e E)
    (p₁₂ pL q₁₂ qL : ZMod 2) :
    (R).comp
      ((R).tensorHom
        ((R).tensorHom (referenceBinaryBlockData b c A B C D hB hC p₁₂ q₁₂).hom
          ((R).id ((R).tensorObj E F)))
        ((R).id ((P).factor (pL + qL + ReferenceCommutor.degree (b + d) e))))
      ((R).comp
        (referenceBinaryBlockData (b + d) e
          ((R).tensorObj ((R).tensorObj A C) ((P).factor q₁₂)) ((R).tensorObj ((R).tensorObj B D) ((P).factor p₁₂)) E F
          (referenceParityProduct_component hB hD p₁₂) hE pL qL).hom
        ((R).tensorHom ((P).orderedLeftDeletion A C E q₁₂ qL).hom
          ((P).orderedLeftDeletion B D F p₁₂ pL).hom)) =
    (R).smul ((-1 : ℝ) ^ (pL * q₁₂ + p₁₂ * q₁₂ + pL * qL +
      (pL + qL + ReferenceCommutor.degree (b + d) e) * ReferenceCommutor.degree b c).val)
      ((R).comp
        ((R).tensorHom
          ((R).tensorHom ((P).rightFactorDeletion ((R).tensorObj ((R).tensorObj A B) ((R).tensorObj C D))
            (p₁₂ + q₁₂ + ReferenceCommutor.degree b c)).hom ((R).id ((R).tensorObj E F)))
          ((R).id ((P).factor (pL + qL + ReferenceCommutor.degree (b + d) e))))
        ((R).comp
          ((P).rightFactorDeletion
            ((R).tensorObj ((R).tensorObj ((R).tensorObj A B) ((R).tensorObj C D)) ((R).tensorObj E F))
            (pL + qL + ReferenceCommutor.degree (b + d) e)).hom
          ((R).comp
            ((R).tensorHom (referenceShuffleData b c A B C D hB hC).hom ((R).id ((R).tensorObj E F)))
            ((R).comp
              (referenceShuffleData (b + d) e ((R).tensorObj A C) ((R).tensorObj B D) E F
                (hB.tensor referenceProperty hD) hE).hom
              ((R).tensorHom ((R).associatorHom A C E) ((R).associatorHom B D F)))))) := by
  have hn := referenceBinaryBlock_leftDeletion (b + d) e
    ((R).tensorObj A C) ((R).tensorObj B D) E F
    (hB.tensor referenceProperty hD) hE q₁₂ p₁₂ pL qL
  have hd := referenceBinaryBlock_deletion (b + d) e
    ((R).tensorObj A C) ((R).tensorObj B D) E F
    (hB.tensor referenceProperty hD) hE pL qL
  have hd₁₂ := referenceBinaryBlock_deletion b c A B C D hB hC p₁₂ q₁₂
  have ho := doubleRightDeletion hR hP ((R).tensorObj E F)
    (p₁₂ + q₁₂ + ReferenceCommutor.degree b c)
    (pL + qL + ReferenceCommutor.degree (b + d) e) (ReferenceCommutor.degree b c)
    (referenceShuffleData b c A B C D hB hC).hom
    (referenceShuffleLaws b c A B C D hB hC).hom_grade
  rw [tensor_orderedLeftDeletion hR hP A C E B D F q₁₂ qL p₁₂ pL,
    (hR).comp_smul, (hR).comp_smul,
    ← (hR).comp_assoc (referenceBinaryBlockData (b + d) e
      ((R).tensorObj ((R).tensorObj A C) ((P).factor q₁₂)) ((R).tensorObj ((R).tensorObj B D) ((P).factor p₁₂)) E F
      (referenceParityProduct_component hB hD p₁₂) hE pL qL).hom, ← hn]
  simp only [(hR).comp_assoc]
  rw [← (hR).comp_assoc _ _ ((R).tensorHom ((R).associatorHom A C E) ((R).associatorHom B D F)), hd]
  simp only [(hR).comp_smul, (hR).smul_comp, ← (hR).mul_smul, ← (hR).comp_assoc]
  rw [← tensor_id_comp hR, ← tensor_id_comp hR, hd₁₂]
  simp only [(hR).tensor_smul_left, (hR).smul_comp, ← (hR).mul_smul]
  rw [ho]
  simp only [(hR).smul_comp, ← (hR).mul_smul, (hR).comp_assoc, ← parity_power_add]
  congr 2
  ring

end RMod.BrundanEllis.Stacking

namespace RMod.BrundanEllis.Stacking
open RMod.Classification
local notation "R" => reference.data.toWeaklyPointedSuperfusionData
local notation "hR" => referenceProperty.toWeaklyPointedSuperfusionLaws
local notation "P" => reference.data.pi
local notation "hP" => referenceProperty.pi

/-- Delete the parity factors in the right binary nesting. The three
parity-interchange signs and the crossing of the outer deletion with the
last shuffle are retained explicitly. -/
theorem referenceRightNesting_deletion (b c d e : ZMod 8) (A B C D E F : (R).Obj)
    (hB : InComponent R b B) (hC : InComponent R c C)
    (hD : InComponent R d D) (hE : InComponent R e E)
    (p₂₃ pR q₂₃ qR : ZMod 2) :
    (R).comp
      ((R).tensorHom
        ((R).tensorHom ((R).id ((R).tensorObj A B))
          (referenceBinaryBlockData d e C D E F hD hE p₂₃ q₂₃).hom)
        ((R).id ((P).factor (pR + qR + ReferenceCommutor.degree b (c + e)))))
      ((R).comp
        (referenceBinaryBlockData b (c + e) A B
          ((R).tensorObj ((R).tensorObj C E) ((P).factor q₂₃)) ((R).tensorObj ((R).tensorObj D F) ((P).factor p₂₃))
          hB (referenceParityProduct_component hC hE q₂₃) pR qR).hom
        ((R).tensorHom ((P).orderedRightDeletion A C E q₂₃ qR).hom
          ((P).orderedRightDeletion B D F p₂₃ pR).hom)) =
    (R).smul ((-1 : ℝ) ^ (pR * q₂₃ + p₂₃ * q₂₃ + pR * qR +
      (pR + qR + ReferenceCommutor.degree b (c + e)) * ReferenceCommutor.degree d e).val)
      ((R).comp ((P).orderedRightDeletion ((R).tensorObj A B) ((R).tensorObj C D) ((R).tensorObj E F)
        (p₂₃ + q₂₃ + ReferenceCommutor.degree d e)
        (pR + qR + ReferenceCommutor.degree b (c + e))).hom
        ((R).comp
          ((R).tensorHom ((R).id ((R).tensorObj A B)) (referenceShuffleData d e C D E F hD hE).hom)
          (referenceShuffleData b (c + e) A B ((R).tensorObj C E) ((R).tensorObj D F)
            hB (hC.tensor referenceProperty hE)).hom)) := by
  have hn := referenceBinaryBlock_rightDeletion b (c + e) A B
    ((R).tensorObj C E) ((R).tensorObj D F)
    hB (hC.tensor referenceProperty hE) q₂₃ p₂₃ pR qR
  have hd := referenceBinaryBlock_deletion b (c + e) A B
    ((R).tensorObj C E) ((R).tensorObj D F)
    hB (hC.tensor referenceProperty hE) pR qR
  have hd₂₃ := referenceBinaryBlock_deletion d e C D E F hD hE p₂₃ q₂₃
  have ho := doubleLeftDeletion hR hP ((R).tensorObj A B)
    (p₂₃ + q₂₃ + ReferenceCommutor.degree d e)
    (pR + qR + ReferenceCommutor.degree b (c + e)) (ReferenceCommutor.degree d e)
    (referenceShuffleData d e C D E F hD hE).hom
    (referenceShuffleLaws d e C D E F hD hE).hom_grade
  rw [tensor_orderedRightDeletion hR hP A C E B D F q₂₃ qR p₂₃ pR,
    (hR).comp_smul, (hR).comp_smul,
    ← (hR).comp_assoc (referenceBinaryBlockData b (c + e) A B
      ((R).tensorObj ((R).tensorObj C E) ((P).factor q₂₃)) ((R).tensorObj ((R).tensorObj D F) ((P).factor p₂₃))
      hB (referenceParityProduct_component hC hE q₂₃) pR qR).hom, ← hn]
  simp only [(hR).comp_assoc]
  rw [hd]
  simp only [(hR).comp_smul, (hR).smul_comp, ← (hR).mul_smul, ← (hR).comp_assoc]
  rw [← tensor_id_comp hR, ← id_tensor_comp hR, hd₂₃]
  simp only [(hR).tensor_smul_right, (hR).tensor_smul_left, (hR).smul_comp, ← (hR).mul_smul]
  rw [ho]
  dsimp only [PiData.orderedRightDeletion, IsoData.trans, IsoData.tensor, IsoData.refl]
  simp only [(hR).smul_comp, ← (hR).mul_smul, (hR).comp_assoc, ← parity_power_add]
  congr 2
  ring

end RMod.BrundanEllis.Stacking
