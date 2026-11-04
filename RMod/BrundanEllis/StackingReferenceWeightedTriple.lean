import RMod.BrundanEllis.StackingReferenceTripleData

/-! Actual binary comparison routes scaled by chosen invertible scalars, together with their forward-map scaling identities. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

namespace RMod.BrundanEllis.Stacking
open RMod.Classification
local notation "raw" => reference.data.toWeaklyPointedSuperfusionData
local notation "tensor" => reference.data.tensorObj
local notation "pi" => reference.data.pi

/-- First compare the first two inputs, then compare their product with
the third input and apply the two original associators. All maps are the
specified binary blocks scaled by the two chosen gauge values, and the original local associators. -/
def referenceWeightedTripleLeftData (b c d e : ZMod 8) (A B C D E F : reference.data.Obj)
    (hB : InComponent raw b B) (hC : InComponent raw c C)
    (hD : InComponent raw d D) (hE : InComponent raw e E)
    (p₁₂ pL p₂₃ pR q₁₂ qL q₂₃ qR : ZMod 2)
    (hp : p₁₂ + pL = p₂₃ + pR) (hq : q₁₂ + qL = q₂₃ + qR)
    (ωs ωt β₁₂ βL : ℝˣ) :
    IsoData raw
      (referenceParityProduct
        (referenceParityProduct (tensor A B) (tensor C D)
          (p₁₂ + q₁₂ + ReferenceCommutor.degree b c))
        (tensor E F) (pL + qL + ReferenceCommutor.degree (b + d) e))
      (tensor (referenceParityProduct A (referenceParityProduct C E q₂₃) qR)
        (referenceParityProduct B (referenceParityProduct D F p₂₃) pR)) :=
  let j₁₂ := (referenceBinaryBlockData b c A B C D hB hC p₁₂ q₁₂).scale raw β₁₂
  let jL := (referenceBinaryBlockData (b + d) e
    (referenceParityProduct A C q₁₂) (referenceParityProduct B D p₁₂) E F
    (referenceParityProduct_component hB hD p₁₂) hE pL qL).scale raw βL
  let aT := (pi).localAssociator A C E q₁₂ qL q₂₃ qR hq ωt
  let aS := (pi).localAssociator B D F p₁₂ pL p₂₃ pR hp ωs
  ((((j₁₂.tensor raw (IsoData.refl raw (tensor E F))).tensor raw
    (IsoData.refl raw ((pi).factor (pL + qL + ReferenceCommutor.degree (b + d) e)))).trans raw jL).trans raw
      (aT.tensor raw aS))

/-- Apply the proposed output associator, compare the last two inputs with the chosen scalar gauges,
and then compare their product with the first input. -/
def referenceWeightedTripleRightData (b c d e : ZMod 8) (A B C D E F : reference.data.Obj)
    (hB : InComponent raw b B) (hC : InComponent raw c C)
    (hD : InComponent raw d D) (hE : InComponent raw e E)
    (p₁₂ pL p₂₃ pR q₁₂ qL q₂₃ qR : ZMod 2)
    (hp : p₁₂ + pL = p₂₃ + pR) (hq : q₁₂ + qL = q₂₃ + qR)
    (ωu β₂₃ βR : ℝˣ) :
    IsoData raw
      (referenceParityProduct
        (referenceParityProduct (tensor A B) (tensor C D)
          (p₁₂ + q₁₂ + ReferenceCommutor.degree b c))
        (tensor E F) (pL + qL + ReferenceCommutor.degree (b + d) e))
      (tensor (referenceParityProduct A (referenceParityProduct C E q₂₃) qR)
        (referenceParityProduct B (referenceParityProduct D F p₂₃) pR)) :=
  let aU := (pi).localAssociator (tensor A B) (tensor C D) (tensor E F)
    (p₁₂ + q₁₂ + ReferenceCommutor.degree b c)
    (pL + qL + ReferenceCommutor.degree (b + d) e)
    (p₂₃ + q₂₃ + ReferenceCommutor.degree d e)
    (pR + qR + ReferenceCommutor.degree b (c + e))
    (referenceTripleParity b c d e p₁₂ pL p₂₃ pR q₁₂ qL q₂₃ qR hp hq) ωu
  let j₂₃ := (referenceBinaryBlockData d e C D E F hD hE p₂₃ q₂₃).scale raw β₂₃
  let jR := (referenceBinaryBlockData b (c + e) A B
    (referenceParityProduct C E q₂₃) (referenceParityProduct D F p₂₃)
    hB (referenceParityProduct_component hC hE q₂₃) pR qR).scale raw βR
  aU.trans raw
    ((((IsoData.refl raw (tensor A B)).tensor raw j₂₃).tensor raw
      (IsoData.refl raw ((pi).factor (pR + qR + ReferenceCommutor.degree b (c + e))))).trans raw jR)



end RMod.BrundanEllis.Stacking

namespace RMod.BrundanEllis.Stacking
open RMod.Classification
local notation "R" => reference.data.toWeaklyPointedSuperfusionData
local notation "hR" => referenceProperty.toWeaklyPointedSuperfusionLaws

/-- Scaling the two actual binary blocks scales their left triple route
by the product of the specified binary scalars. -/
theorem referenceWeightedTripleLeft_hom (b c d e : ZMod 8) (A B C D E F : (R).Obj)
    (hB : InComponent R b B) (hC : InComponent R c C)
    (hD : InComponent R d D) (hE : InComponent R e E)
    (p₁₂ pL p₂₃ pR q₁₂ qL q₂₃ qR : ZMod 2)
    (hp : p₁₂ + pL = p₂₃ + pR) (hq : q₁₂ + qL = q₂₃ + qR) (ωs ωt β₁₂ βL : ℝˣ) :
    (referenceWeightedTripleLeftData b c d e A B C D E F hB hC hD hE
      p₁₂ pL p₂₃ pR q₁₂ qL q₂₃ qR hp hq ωs ωt β₁₂ βL).hom =
    (R).smul (β₁₂.val * βL.val)
      (referenceTripleLeftData b c d e A B C D E F hB hC hD hE
        p₁₂ pL p₂₃ pR q₁₂ qL q₂₃ qR hp hq ωs ωt).hom := by
  dsimp only [referenceWeightedTripleLeftData, referenceTripleLeftData,
    IsoData.trans, IsoData.tensor, IsoData.refl, IsoData.scale]
  simp only [(hR).tensor_smul_left, (hR).smul_comp, (hR).comp_smul, ← (hR).mul_smul]

/-- Scaling the last and outer binary blocks gives the analogous product
on the right triple route. -/
theorem referenceWeightedTripleRight_hom (b c d e : ZMod 8) (A B C D E F : (R).Obj)
    (hB : InComponent R b B) (hC : InComponent R c C)
    (hD : InComponent R d D) (hE : InComponent R e E)
    (p₁₂ pL p₂₃ pR q₁₂ qL q₂₃ qR : ZMod 2)
    (hp : p₁₂ + pL = p₂₃ + pR) (hq : q₁₂ + qL = q₂₃ + qR) (ωu β₂₃ βR : ℝˣ) :
    (referenceWeightedTripleRightData b c d e A B C D E F hB hC hD hE
      p₁₂ pL p₂₃ pR q₁₂ qL q₂₃ qR hp hq ωu β₂₃ βR).hom =
    (R).smul (β₂₃.val * βR.val)
      (referenceTripleRightData b c d e A B C D E F hB hC hD hE
        p₁₂ pL p₂₃ pR q₁₂ qL q₂₃ qR hp hq ωu).hom := by
  dsimp only [referenceWeightedTripleRightData, referenceTripleRightData,
    IsoData.trans, IsoData.tensor, IsoData.refl, IsoData.scale]
  simp only [(hR).tensor_smul_right, (hR).tensor_smul_left,
    (hR).smul_comp, (hR).comp_smul, ← (hR).mul_smul]

/-- The output scalar is linear in the right triple route, as it is in
the local associator defining that route. -/
theorem referenceTripleRight_scalar (b c d e : ZMod 8) (A B C D E F : (R).Obj)
    (hB : InComponent R b B) (hC : InComponent R c C)
    (hD : InComponent R d D) (hE : InComponent R e E)
    (p₁₂ pL p₂₃ pR q₁₂ qL q₂₃ qR : ZMod 2)
    (hp : p₁₂ + pL = p₂₃ + pR) (hq : q₁₂ + qL = q₂₃ + qR) (ωu : ℝˣ) :
    (referenceTripleRightData b c d e A B C D E F hB hC hD hE
      p₁₂ pL p₂₃ pR q₁₂ qL q₂₃ qR hp hq ωu).hom =
    (R).smul ωu.val
      (referenceTripleRightData b c d e A B C D E F hB hC hD hE
        p₁₂ pL p₂₃ pR q₁₂ qL q₂₃ qR hp hq 1).hom := by
  dsimp only [referenceTripleRightData, PiData.localAssociator,
    IsoData.trans, IsoData.tensor, IsoData.refl, IsoData.scale]
  simp only [Units.val_one, (hR).one_smul, (hR).smul_comp]

end RMod.BrundanEllis.Stacking
