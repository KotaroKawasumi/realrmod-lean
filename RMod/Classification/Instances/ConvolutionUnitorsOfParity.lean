import RMod.Classification.Instances.SingleBiproduct
import RMod.Classification.Proofs.ConvolutionUnitSupport
import RMod.Classification.Proofs.Parameters

/-!
# Convolution unitors before scalar coherence

Only normalization of the parity cochain is used in these data.

Project onto the only potentially nonzero summand, identify the supported
unit and the normalized zero parity factor, and use C's unitors. The
inverse follows the reverse comparisons and the corresponding inclusion.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData)

noncomputable def convolutionLeftUnitBlockOfParity (hν : ∀ g : t.group, t.nu 1 g = 0) (X : PullbackObj C t) (k : t.group) :
    convolutionEvenFamily C hC t (pullbackUnitObj C hC t) X k 1 ≅ referenceEvenObj C hC (X k).val := by
  let X₀ : t.group → C.Obj := fun a => (X a).val
  change referenceEvenObj C hC (C.tensorObj
      (C.tensorObj (pullbackUnitObj C hC t 1).val (X₀ (1⁻¹ * k)))
      (C.pi.factor (t.nu 1 (1⁻¹ * k)))) ≅ referenceEvenObj C hC (X₀ k)
  rw [inv_one, one_mul, hν]
  simp only [pullbackUnitObj, supportedObj_one, PiData.factor]
  exact (ρ_ (𝟙_ (ReferenceEvenCategory C hC) ⊗ referenceEvenObj C hC (X₀ k))) ≪≫
    (λ_ (referenceEvenObj C hC (X₀ k)))

noncomputable def convolutionRightUnitBlockOfParity (hν : ∀ g : t.group, t.nu g 1 = 0) (X : PullbackObj C t) (k : t.group) :
    convolutionEvenFamily C hC t X (pullbackUnitObj C hC t) k k ≅ referenceEvenObj C hC (X k).val := by
  let U₀ : t.group → C.Obj := fun a => (pullbackUnitObj C hC t a).val
  change referenceEvenObj C hC (C.tensorObj (C.tensorObj (X k).val (U₀ (k⁻¹ * k)))
      (C.pi.factor (t.nu k (k⁻¹ * k)))) ≅ referenceEvenObj C hC (X k).val
  rw [inv_mul_cancel, hν]
  simp only [U₀, pullbackUnitObj, supportedObj_one, PiData.factor]
  exact (ρ_ (referenceEvenObj C hC (X k).val ⊗ 𝟙_ (ReferenceEvenCategory C hC))) ≪≫
    (ρ_ (referenceEvenObj C hC (X k).val))

noncomputable def convolutionLeftUnitorEvenIsoOfParity (hν : ∀ g : t.group, t.nu 1 g = 0) (X : PullbackObj C t) (k : t.group) :
    referenceEvenObj C hC (convolutionObj C hC t (pullbackUnitObj C hC t) X k).val ≅
      referenceEvenObj C hC (X k).val :=
  convolutionEvenIso C hC t (pullbackUnitObj C hC t) X k ≪≫
    biproductSingleIso _ 1 (fun g hg => convolutionUnitLeft_isZero C hC t X k g hg) ≪≫
    convolutionLeftUnitBlockOfParity C hC t hν X k

noncomputable def convolutionRightUnitorEvenIsoOfParity (hν : ∀ g : t.group, t.nu g 1 = 0) (X : PullbackObj C t) (k : t.group) :
    referenceEvenObj C hC (convolutionObj C hC t X (pullbackUnitObj C hC t) k).val ≅
      referenceEvenObj C hC (X k).val :=
  convolutionEvenIso C hC t X (pullbackUnitObj C hC t) k ≪≫
    biproductSingleIso _ k (fun g hg => convolutionUnitRight_isZero C hC t X k g hg) ≪≫
    convolutionRightUnitBlockOfParity C hC t hν X k

noncomputable def convolutionLeftUnitorDataOfParity (hν : ∀ g : t.group, t.nu 1 g = 0) (X : PullbackObj C t) (k : t.group) :
    IsoData C.toWeaklyPointedSuperfusionData
      (convolutionObj C hC t (pullbackUnitObj C hC t) X k).val (X k).val :=
  IsoData.ofEvenIso ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩
    (convolutionLeftUnitorEvenIsoOfParity C hC t hν X k)

noncomputable def convolutionRightUnitorDataOfParity (hν : ∀ g : t.group, t.nu g 1 = 0) (X : PullbackObj C t) (k : t.group) :
    IsoData C.toWeaklyPointedSuperfusionData
      (convolutionObj C hC t X (pullbackUnitObj C hC t) k).val (X k).val :=
  IsoData.ofEvenIso ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩
    (convolutionRightUnitorEvenIsoOfParity C hC t hν X k)

end RMod.Classification
