import RMod.BrundanEllis.StackingReferenceNestingDeletion
import RMod.BrundanEllis.StackingReferenceTripleDeletion
import RMod.BrundanEllis.StackingReferenceShuffleAssociativity

/-! Evaluate both actual triple routes against a common target deletion. The left route retains the explicit reference shuffle defect. -/

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

/-- The scalar obtained from the actual left triple comparison is the
product of the input scalars, the parity-deletion sign, and the verified
reference-shuffle defect. -/
theorem referenceTripleLeft_deletion (b c d e : ZMod 8)
    (hl : ReferenceCommutor.LeftEquation b c e) (hr : ReferenceCommutor.RightEquation b d e)
    (A B C D E F : (R).Obj)
    (hB : InComponent R b B) (hC : InComponent R c C)
    (hD : InComponent R d D) (hE : InComponent R e E)
    (p₁₂ pL p₂₃ pR q₁₂ qL q₂₃ qR : ZMod 2)
    (hp : p₁₂ + pL = p₂₃ + pR) (hq : q₁₂ + qL = q₂₃ + qR) (ωs ωt : ℝˣ) :
    (R).comp
      (referenceTripleLeftData b c d e A B C D E F hB hC hD hE
        p₁₂ pL p₂₃ pR q₁₂ qL q₂₃ qR hp hq ωs ωt).hom
      (referenceTripleTargetDeletionData A B C D E F p₂₃ pR q₂₃ qR).hom =
    (R).smul (ωt.val * ωs.val * (-1 : ℝ) ^
      (pL * q₁₂ + p₁₂ * q₁₂ + pL * qL +
        (pL + qL + ReferenceCommutor.degree (b + d) e) * ReferenceCommutor.degree b c +
        (ReferenceCommutor.rightDefect b d e + ReferenceCommutor.degree b c * ReferenceCommutor.degree d e)).val)
      (referenceTripleReducedData b c d e A B C D E F hB hC hD hE p₁₂ pL q₁₂ qL).hom := by
  have hn := referenceLeftNesting_deletion b c d e A B C D E F hB hC hD hE p₁₂ pL q₁₂ qL
  have hs := referenceShuffle_associativity b c d e hl hr A B C D E F hB hC hD hE
  dsimp only [referenceTripleLeftData, referenceTripleTargetDeletionData,
    IsoData.trans, IsoData.tensor, IsoData.refl, IsoData.homogeneousTensor, referenceParityProduct]
  simp only [(hR).comp_assoc]
  rw [tensor_localAssociator_orderedDeletion hR hP A C E B D F
    q₁₂ qL q₂₃ qR p₁₂ pL p₂₃ pR hq hp ωt ωs]
  simp only [(hR).comp_smul]
  rw [hn]
  rw [hs]
  dsimp only [referenceTripleReducedData, PiData.orderedLeftDeletion,
    IsoData.trans, IsoData.tensor, IsoData.refl, IsoData.assoc]
  simp only [(hR).comp_smul, ← (hR).mul_smul, (hR).comp_assoc, mul_assoc, ← parity_power_add]

/-- The actual right triple comparison has the proposed output scalar
and the parity-deletion sign; its remaining map is the same reduced route. -/
theorem referenceTripleRight_deletion (b c d e : ZMod 8) (A B C D E F : (R).Obj)
    (hB : InComponent R b B) (hC : InComponent R c C)
    (hD : InComponent R d D) (hE : InComponent R e E)
    (p₁₂ pL p₂₃ pR q₁₂ qL q₂₃ qR : ZMod 2)
    (hp : p₁₂ + pL = p₂₃ + pR) (hq : q₁₂ + qL = q₂₃ + qR) (ωu : ℝˣ) :
    (R).comp
      (referenceTripleRightData b c d e A B C D E F hB hC hD hE
        p₁₂ pL p₂₃ pR q₁₂ qL q₂₃ qR hp hq ωu).hom
      (referenceTripleTargetDeletionData A B C D E F p₂₃ pR q₂₃ qR).hom =
    (R).smul (ωu.val * (-1 : ℝ) ^
      (pR * q₂₃ + p₂₃ * q₂₃ + pR * qR +
        (pR + qR + ReferenceCommutor.degree b (c + e)) * ReferenceCommutor.degree d e).val)
      (referenceTripleReducedData b c d e A B C D E F hB hC hD hE p₁₂ pL q₁₂ qL).hom := by
  have hn := referenceRightNesting_deletion b c d e A B C D E F hB hC hD hE p₂₃ pR q₂₃ qR
  dsimp only [referenceTripleRightData, referenceTripleTargetDeletionData,
    IsoData.trans, IsoData.tensor, IsoData.refl, IsoData.homogeneousTensor, referenceParityProduct]
  simp only [(hR).comp_assoc]
  rw [hn, (hR).comp_smul, ← (hR).comp_assoc,
    (hP).localAssociator_orderedDeletion hR]
  dsimp only [referenceTripleReducedData, IsoData.trans, IsoData.tensor, IsoData.refl]
  simp only [(hR).smul_comp, ← (hR).mul_smul, (hR).comp_assoc]
  rw [mul_comm _ ωu.val]

end RMod.BrundanEllis.Stacking
