import RMod.BrundanEllis.StackingReferenceBinaryBlock
import RMod.BrundanEllis.StackingReferenceComponentHexagonNaturality
import RMod.Classification.Proofs.OrderedParityDeletion
import RMod.Classification.Proofs.HomogeneousTensorIso

/-! Concrete left and right triple comparison data and their common parity-deleted route. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

namespace RMod.BrundanEllis.Stacking
open RMod.Classification
local notation "raw" => reference.data.toWeaklyPointedSuperfusionData
local notation "tensor" => reference.data.tensorObj
local notation "pi" => reference.data.pi

/-- A reference tensor product with its specified right parity factor. -/
def referenceParityProduct (X Y : reference.data.Obj) (a : ZMod 2) : reference.data.Obj :=
  tensor (tensor X Y) ((pi).factor a)

/-- The parity factor does not change the reference component. -/
theorem referenceParityProduct_component {a b : ZMod 8} {X Y : reference.data.Obj}
    (hX : InComponent raw a X) (hY : InComponent raw b Y) (p : ZMod 2) :
    InComponent raw (a + b) (referenceParityProduct X Y p) := by
  simpa only [referenceParityProduct, add_zero] using
    (hX.tensor referenceProperty hY).tensor referenceProperty
      (InComponent.parity_factor referenceProperty p)

/-- The input cocycles and bilinearity of the crossing degree identify
exactly the two total parity factors of the comparison associator. -/
theorem referenceTripleParity (b c d e : ZMod 8)
    (p₁₂ pL p₂₃ pR q₁₂ qL q₂₃ qR : ZMod 2)
    (hp : p₁₂ + pL = p₂₃ + pR) (hq : q₁₂ + qL = q₂₃ + qR) :
    (p₁₂ + q₁₂ + ReferenceCommutor.degree b c) +
      (pL + qL + ReferenceCommutor.degree (b + d) e) =
    (p₂₃ + q₂₃ + ReferenceCommutor.degree d e) +
      (pR + qR + ReferenceCommutor.degree b (c + e)) := by
  rw [referenceDegree_add_left, referenceDegree_add_right]
  linear_combination hp + hq

/-- First compare the first two inputs, then compare their product with
the third input and apply the two original associators. All maps are the
already specified binary blocks and local associators. -/
def referenceTripleLeftData (b c d e : ZMod 8) (A B C D E F : reference.data.Obj)
    (hB : InComponent raw b B) (hC : InComponent raw c C)
    (hD : InComponent raw d D) (hE : InComponent raw e E)
    (p₁₂ pL p₂₃ pR q₁₂ qL q₂₃ qR : ZMod 2)
    (hp : p₁₂ + pL = p₂₃ + pR) (hq : q₁₂ + qL = q₂₃ + qR)
    (ωs ωt : ℝˣ) :
    IsoData raw
      (referenceParityProduct
        (referenceParityProduct (tensor A B) (tensor C D)
          (p₁₂ + q₁₂ + ReferenceCommutor.degree b c))
        (tensor E F) (pL + qL + ReferenceCommutor.degree (b + d) e))
      (tensor (referenceParityProduct A (referenceParityProduct C E q₂₃) qR)
        (referenceParityProduct B (referenceParityProduct D F p₂₃) pR)) :=
  let j₁₂ := referenceBinaryBlockData b c A B C D hB hC p₁₂ q₁₂
  let jL := referenceBinaryBlockData (b + d) e
    (referenceParityProduct A C q₁₂) (referenceParityProduct B D p₁₂) E F
    (referenceParityProduct_component hB hD p₁₂) hE pL qL
  let aT := (pi).localAssociator A C E q₁₂ qL q₂₃ qR hq ωt
  let aS := (pi).localAssociator B D F p₁₂ pL p₂₃ pR hp ωs
  ((((j₁₂.tensor raw (IsoData.refl raw (tensor E F))).tensor raw
    (IsoData.refl raw ((pi).factor (pL + qL + ReferenceCommutor.degree (b + d) e)))).trans raw jL).trans raw
      (aT.tensor raw aS))

/-- Apply the proposed output associator, compare the last two inputs,
and then compare their product with the first input. -/
def referenceTripleRightData (b c d e : ZMod 8) (A B C D E F : reference.data.Obj)
    (hB : InComponent raw b B) (hC : InComponent raw c C)
    (hD : InComponent raw d D) (hE : InComponent raw e E)
    (p₁₂ pL p₂₃ pR q₁₂ qL q₂₃ qR : ZMod 2)
    (hp : p₁₂ + pL = p₂₃ + pR) (hq : q₁₂ + qL = q₂₃ + qR)
    (ωu : ℝˣ) :
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
  let j₂₃ := referenceBinaryBlockData d e C D E F hD hE p₂₃ q₂₃
  let jR := referenceBinaryBlockData b (c + e) A B
    (referenceParityProduct C E q₂₃) (referenceParityProduct D F p₂₃)
    hB (referenceParityProduct_component hC hE q₂₃) pR qR
  aU.trans raw
    ((((IsoData.refl raw (tensor A B)).tensor raw j₂₃).tensor raw
      (IsoData.refl raw ((pi).factor (pR + qR + ReferenceCommutor.degree b (c + e))))).trans raw jR)


/-- Delete the target parity factors in each component, using the signed
tensor inverse appropriate to the two homogeneous deletion maps. -/
def referenceTripleTargetDeletionData (A B C D E F : reference.data.Obj)
    (p₂₃ pR q₂₃ qR : ZMod 2) :
    IsoData raw
      (tensor (referenceParityProduct A (referenceParityProduct C E q₂₃) qR)
        (referenceParityProduct B (referenceParityProduct D F p₂₃) pR))
      (tensor (tensor A (tensor C E)) (tensor B (tensor D F))) :=
  ((pi).orderedRightDeletion A C E q₂₃ qR).homogeneousTensor raw (q₂₃ + qR) (p₂₃ + pR)
    ((pi).orderedRightDeletion B D F p₂₃ pR)


/-- The common route after deleting the source parities: reassociate the
three paired inputs, exchange the last middle pair, then the remaining
block. Both corrected triple routes will be compared to this actual map. -/
def referenceTripleReducedData (b c d e : ZMod 8) (A B C D E F : reference.data.Obj)
    (hB : InComponent raw b B) (hC : InComponent raw c C)
    (hD : InComponent raw d D) (hE : InComponent raw e E)
    (p₁₂ pL q₁₂ qL : ZMod 2) :
    IsoData raw
      (referenceParityProduct
        (referenceParityProduct (tensor A B) (tensor C D)
          (p₁₂ + q₁₂ + ReferenceCommutor.degree b c))
        (tensor E F) (pL + qL + ReferenceCommutor.degree (b + d) e))
      (tensor (tensor A (tensor C E)) (tensor B (tensor D F))) :=
  let source := (pi).orderedLeftDeletion (tensor A B) (tensor C D) (tensor E F)
    (p₁₂ + q₁₂ + ReferenceCommutor.degree b c)
    (pL + qL + ReferenceCommutor.degree (b + d) e)
  let j₂₃ := referenceShuffleData d e C D E F hD hE
  let jR := referenceShuffleData b (c + e) A B (tensor C E) (tensor D F)
    hB (hC.tensor referenceProperty hE)
  source.trans raw (((IsoData.refl raw (tensor A B)).tensor raw j₂₃).trans raw jR)

end RMod.BrundanEllis.Stacking
