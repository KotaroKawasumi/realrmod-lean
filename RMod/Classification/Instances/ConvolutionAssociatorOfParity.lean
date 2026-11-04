import RMod.Classification.Instances.ConvolutionExpansion
import RMod.Classification.Proofs.Normalizers
import RMod.Classification.Proofs.Parameters

/-!
# The convolution associator before scalar coherence

Only the parity cocycle is needed for this data construction.
No normalization or pentagon equation for omega is assumed.

Expand the two iterated sums, reindex (a,g) as (g,g^-1 a), and apply the
specified local omega times R-inverse L in each block. The reverse maps
of these even isomorphisms give the inverse associator. Its pentagon and
naturality remain separate obligations on this fixed construction.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory CategoryTheory.Limits

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData)

def convolutionAssocIndex : ((_ : t.group) × t.group) ≃ ((_ : t.group) × t.group) where
  toFun i := ⟨i.2, i.2⁻¹ * i.1⟩
  invFun i := ⟨i.1 * i.2, i.1⟩
  left_inv i := by cases i; simp
  right_inv i := by cases i; simp

noncomputable def convolutionBlockIsoOfParity (hν : ∀ g h l : t.group, t.nu g h + t.nu (g * h) l = t.nu h l + t.nu g (h * l)) (X Y Z : PullbackObj C t)
    (k g h : t.group) :
    convolutionLeftFamily C hC t X Y Z k (g * h) g ≅ convolutionRightFamily C hC t X Y Z k g h := by
  let X₀ : t.group → C.Obj := fun a => (X a).val
  let Y₀ : t.group → C.Obj := fun a => (Y a).val
  let Z₀ : t.group → C.Obj := fun a => (Z a).val
  change referenceEvenObj C hC
      (C.tensorObj (C.tensorObj (C.tensorObj (C.tensorObj (X₀ g) (Y₀ (g⁻¹ * (g * h))))
        (C.pi.factor (t.nu g (g⁻¹ * (g * h))))) (Z₀ ((g * h)⁻¹ * k)))
        (C.pi.factor (t.nu (g * h) ((g * h)⁻¹ * k)))) ≅
    referenceEvenObj C hC
      (C.tensorObj (C.tensorObj (X₀ g) (C.tensorObj (C.tensorObj (Y₀ h) (Z₀ (h⁻¹ * (g⁻¹ * k))))
        (C.pi.factor (t.nu h (h⁻¹ * (g⁻¹ * k)))))) (C.pi.factor (t.nu g (g⁻¹ * k))))
  let l := (g * h)⁻¹ * k
  have he := (C.pi.localAssociator (X₀ g) (Y₀ h) (Z₀ l)
    (t.nu g h) (t.nu (g * h) l) (t.nu h l) (t.nu g (h * l))
    (hν g h l) (t.omega g h l)).toEvenIso
      ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩
      (hC.pi.localAssociator_evenIso hC.toWeaklyPointedSuperfusionLaws _ _ _ _ _ _ _ _ _)
  simpa only [l, mul_inv_rev, mul_assoc, inv_mul_cancel_left, mul_inv_cancel_left] using he

noncomputable def convolutionBlocksIsoOfParity (hν : ∀ g h l : t.group, t.nu g h + t.nu (g * h) l = t.nu h l + t.nu g (h * l)) (X Y Z : PullbackObj C t) (k : t.group) :
    (⨁ fun i : (_ : t.group) × t.group => convolutionLeftFamily C hC t X Y Z k i.1 i.2) ≅
      ⨁ fun i : (_ : t.group) × t.group => convolutionRightFamily C hC t X Y Z k i.1 i.2 :=
  biproduct.whiskerEquiv (convolutionAssocIndex t) (fun i => by
    change convolutionRightFamily C hC t X Y Z k i.2 (i.2⁻¹ * i.1) ≅
      convolutionLeftFamily C hC t X Y Z k i.1 i.2
    have he := (convolutionBlockIsoOfParity C hC t hν X Y Z k i.2 (i.2⁻¹ * i.1)).symm
    simpa only [mul_inv_cancel_left] using he)

noncomputable def convolutionAssociatorEvenIsoOfParity (hν : ∀ g h l : t.group, t.nu g h + t.nu (g * h) l = t.nu h l + t.nu g (h * l))
    (X Y Z : PullbackObj C t) (k : t.group) :
    referenceEvenObj C hC (convolutionObj C hC t (convolutionObj C hC t X Y) Z k).val ≅
      referenceEvenObj C hC (convolutionObj C hC t X (convolutionObj C hC t Y Z) k).val :=
  convolutionLeftExpand C hC t X Y Z k ≪≫ convolutionBlocksIsoOfParity C hC t hν X Y Z k ≪≫
    (convolutionRightExpand C hC t X Y Z k).symm

noncomputable def convolutionAssociatorDataOfParity (hν : ∀ g h l : t.group, t.nu g h + t.nu (g * h) l = t.nu h l + t.nu g (h * l))
    (X Y Z : PullbackObj C t) (k : t.group) :
    IsoData C.toWeaklyPointedSuperfusionData
      (convolutionObj C hC t (convolutionObj C hC t X Y) Z k).val
      (convolutionObj C hC t X (convolutionObj C hC t Y Z) k).val :=
  IsoData.ofEvenIso ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩
    (convolutionAssociatorEvenIsoOfParity C hC t hν X Y Z k)

end RMod.Classification
