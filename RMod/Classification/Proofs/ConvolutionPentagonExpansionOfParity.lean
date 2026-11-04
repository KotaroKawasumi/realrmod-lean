import RMod.Classification.Instances.ConvolutionPentagonRoutesOfParity
import RMod.Classification.Proofs.ConvolutionFourWhiskerEdgesOfParity
import RMod.Classification.Proofs.ConvolutionFourMiddleEdgesOfParity
import Mathlib.CategoryTheory.CommSq

/-!
The only parameter law used in this file is the parity cocycle.
No scalar normalization or pentagon for omega is assumed.

# Both convolution pentagon paths on a fourfold summand

Compose the five checked insertion squares using Mathlib's horizontal
composition of commutative squares. The resulting block paths retain
all five actual scalar-weighted associators.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData)
  (hν : ∀ g h k : t.group, t.nu g h + t.nu (g * h) k = t.nu h k + t.nu g (h * k))

theorem convolutionPentagonThreeOfParity_inclusion (W X Y Z : PullbackObj C t) (k g h l : t.group) :
    C.comp (convolutionFourLeftInsertion C hC t W X Y Z k (g * (h * l)) (g * h) g).hom
      (convolutionPentagonThreeOfParity C hC t hν W X Y Z k) =
    C.comp (convolutionBlockPentagonThreeOfParity C hC t hν W X Y Z k g h l).hom.hom
      (convolutionFourRightInsertion C hC t W X Y Z k g h l).hom := by
  let A : WeaklyPointedSuperfusion := ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩
  have h₁ := convolutionFourLeftInsertion_firstOfParity C hC t hν W X Y Z k (g * (h * l)) g h
  have h₂ := convolutionFourInnerInsertion_middleOfParity C hC t hν W X Y Z k g (h * l) h
  have h₃ := convolutionFourOuterInsertion_lastOfParity C hC t hν W X Y Z k g h l
  have s₁ : CommSq (C := LinearCategory A) _ _ _ _ := ⟨h₁.symm⟩
  have s₂ : CommSq (C := LinearCategory A) _ _ _ _ := ⟨h₂.symm⟩
  have s₃ : CommSq (C := LinearCategory A) _ _ _ _ := ⟨h₃.symm⟩
  exact ((s₁.horiz_comp s₂).horiz_comp s₃).w.symm

theorem convolutionPentagonTwoOfParity_inclusion (W X Y Z : PullbackObj C t) (k g h l : t.group) :
    C.comp (convolutionFourLeftInsertion C hC t W X Y Z k ((g * h) * l) (g * h) g).hom
      (convolutionPentagonTwoOfParity C hC t hν W X Y Z k) =
    C.comp (convolutionBlockPentagonTwoOfParity C hC t hν W X Y Z k g h l).hom.hom
      (convolutionFourRightInsertion C hC t W X Y Z k g h l).hom := by
  let A : WeaklyPointedSuperfusion := ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩
  have h₁ := convolutionFourLeftInsertion_short_firstOfParity C hC t hν W X Y Z k (g * h) l g
  have h₂ := convolutionFourMiddleInsertion_short_lastOfParity C hC t hν W X Y Z k g h l
  have s₁ : CommSq (C := LinearCategory A) _ _ _ _ := ⟨h₁.symm⟩
  have s₂ : CommSq (C := LinearCategory A) _ _ _ _ := ⟨h₂.symm⟩
  exact (s₁.horiz_comp s₂).w.symm

end RMod.Classification
