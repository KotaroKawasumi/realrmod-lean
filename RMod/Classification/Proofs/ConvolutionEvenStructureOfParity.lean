import RMod.Classification.Instances.ConvolutionEvenStructureOfParity
import RMod.Classification.Abstract.MonoidalComparison
import RMod.Classification.Proofs.ConvolutionNaturality
import RMod.Classification.Proofs.ConvolutionUnitNaturality

/-!
# Bifunctoriality and naturality on the even convolution category

Even maps have trivial interchange sign. The other laws are the existing
convolution naturality theorems, now stated with only parity hypotheses.
These checks precede, and do not assume, scalar normalization or pentagon.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory Superfusion.Category

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData)
  (hν : ∀ g h k : t.group, t.nu g h + t.nu (g * h) k = t.nu h k + t.nu g (h * k))
  (hνL : ∀ g : t.group, t.nu 1 g = 0) (hνR : ∀ g : t.group, t.nu g 1 = 0)

theorem convolutionEven_tensorStructuralLawsOfParity :
    letI := convolutionEvenMonoidalStructOfParity C hC t hν hνL hνR
    TensorStructuralLaws (EvenSubcategory ℝ (PullbackCategory C hC t)) := by
  letI := convolutionEvenMonoidalStructOfParity C hC t hν hνL hνR
  refine
    { tensor_id := ?_
      tensor_comp := ?_
      whisker_left := fun _ {_ _} _ => rfl
      whisker_right := fun {_ _} _ _ => rfl
      associator_naturality := ?_
      left_unitor_naturality := ?_
      right_unitor_naturality := ?_ }
  · intro X Y
    apply WideSubcategory.hom_ext
    exact convolutionHom_id C hC t X.obj Y.obj
  · intro X₁ X₂ X₃ Y₁ Y₂ Y₃ f g h k
    apply WideSubcategory.hom_ext
    symm
    have he := convolutionHom_interchange C hC t g.hom k.hom f.hom h.hom 0 0 k.property f.property
    simp only [mul_zero, ZMod.val_zero, pow_zero, hC.one_smul] at he
    exact he
  · intro X₁ X₂ X₃ Y₁ Y₂ Y₃ f g h
    apply WideSubcategory.hom_ext
    funext q
    exact convolutionAssociatorOfParity_naturality C hC t hν f.hom g.hom h.hom q
  · intro X Y f
    apply WideSubcategory.hom_ext
    funext q
    exact convolutionLeftUnitorOfParity_naturality C hC t hνL f.hom q
  · intro X Y f
    apply WideSubcategory.hom_ext
    funext q
    exact convolutionRightUnitorOfParity_naturality C hC t hνR f.hom q

end RMod.Classification
