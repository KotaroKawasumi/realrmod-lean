import RMod.Classification.Proofs.ConvolutionPentagonExpansionOfParity
import RMod.Classification.Proofs.ConvolutionSplitInclusions
import RMod.Classification.Proofs.HomHEq

/-!
# Restricting a global pentagon to its actual fourfold blocks

The expansion equations identify both paths on every source inclusion.
Their source indices differ only by group associativity. The common
target inclusion has a retraction, so cancelling it recovers equality
of the specified local block paths. No scalar equation is assumed.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData)
  (hν : ∀ g h k : t.group, t.nu g h + t.nu (g * h) k = t.nu h k + t.nu g (h * k))

theorem convolutionBlockPentagon_heq_of_eq (W X Y Z : PullbackObj C t) (k g h l : t.group)
    (hp : convolutionPentagonThreeOfParity C hC t hν W X Y Z k =
      convolutionPentagonTwoOfParity C hC t hν W X Y Z k) :
    HEq (convolutionBlockPentagonThreeOfParity C hC t hν W X Y Z k g h l).hom.hom
      (convolutionBlockPentagonTwoOfParity C hC t hν W X Y Z k g h l).hom.hom := by
  have hs := congrArg
    (fun a => (convolutionFourLeftFamily C hC t W X Y Z k a (g * h) g).obj)
    (mul_assoc g h l).symm
  have hi := congr_arg_heq
    (fun a => (convolutionFourLeftInsertion C hC t W X Y Z k a (g * h) g).hom)
    (mul_assoc g h l).symm
  have he := HomTransport.comp_heq C.toWeaklyPointedSuperfusionData hs rfl rfl hi
    (HEq.refl (convolutionPentagonThreeOfParity C hC t hν W X Y Z k))
  have he' := congrArg
    (C.comp (convolutionFourLeftInsertion C hC t W X Y Z k ((g * h) * l) (g * h) g).hom) hp
  have h₁ := convolutionPentagonThreeOfParity_inclusion C hC t hν W X Y Z k g h l
  have h₂ := convolutionPentagonTwoOfParity_inclusion C hC t hν W X Y Z k g h l
  have hb := (heq_of_eq h₁.symm).trans (he.trans ((heq_of_eq he').trans (heq_of_eq h₂)))
  let j := convolutionFourRightInsertion C hC t W X Y Z k g h l
  exact HomTransport.cancel_postcomp_heq C.toWeaklyPointedSuperfusionData
    hC.toWeaklyPointedSuperfusionLaws hs j.hom (retraction j).hom
    (congrArg (fun f => f.hom) (IsSplitMono.id j)) hb

end RMod.Classification
