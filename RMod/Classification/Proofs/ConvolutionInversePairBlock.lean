import RMod.Classification.Instances.ConvolutionInversePairBlock
import RMod.Classification.Proofs.ConvolutionBlocks

/-!
# The actual associator on the inverse-pair summand

Mathlib equality naturality transports the source inclusion from the
identity label to g*g⁻¹. The already proved associator block equation then
applies without changing either morphism in the convolution construction.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData) (ht : TwistLaws t)

theorem convolutionAssociator_inverse_pair_inclusion (X Y Z : PullbackObj C t) (k g : t.group) :
    C.comp (convolutionLeftInsertionEven C hC t X Y Z k 1 g).hom
      (convolutionAssociatorData C hC t ht X Y Z k).hom =
      C.comp (convolutionInversePairBlock C hC t ht X Y Z k g).hom.hom
        (convolutionRightInsertionEven C hC t X Y Z k g g⁻¹).hom := by
  have hi := eqToHom_naturality
    (fun a => convolutionLeftInsertionEven C hC t X Y Z k a g) (mul_inv_cancel g).symm
  simp only [eqToHom_refl, Category.comp_id] at hi
  have he : convolutionLeftInsertionEven C hC t X Y Z k 1 g ≫
      (convolutionAssociatorEvenIso C hC t ht X Y Z k).hom =
      (convolutionInversePairBlock C hC t ht X Y Z k g).hom ≫
        convolutionRightInsertionEven C hC t X Y Z k g g⁻¹ := by
    rw [hi, Category.assoc, convolutionAssociator_inclusion]
    simp only [convolutionInversePairBlock, Iso.trans_hom, eqToIso.hom, Category.assoc]
  exact congrArg (fun f => f.hom) he

end RMod.Classification
