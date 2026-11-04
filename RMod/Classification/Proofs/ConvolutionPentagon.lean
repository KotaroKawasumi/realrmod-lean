import RMod.Classification.Proofs.ConvolutionBlockPentagon
import RMod.Classification.Proofs.HomHEq

/-!
# The full pentagon for the constructed pullback tensor

The two block routes agree by the weighted local pentagon. Their only
source discrepancy is group associativity, transported by dependent
congruence. The fourfold summand test therefore proves equality of the
actual global composites, with no additional coherence hypothesis.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData)
  (ht : TwistLaws t)

theorem convolution_pentagon (W X Y Z : PullbackObj C t) (k : t.group) :
    convolutionPentagonThree C hC t ht W X Y Z k =
      convolutionPentagonTwo C hC t ht W X Y Z k := by
  apply hom_ext_of_convolutionFourLeftInsertions_degrees C hC t W X Y Z k
  intro g h l
  have hs := congrArg
    (fun a => (convolutionFourLeftFamily C hC t W X Y Z k a (g * h) g).obj) (mul_assoc g h l).symm
  have hi := congr_arg_heq
    (fun a => (convolutionFourLeftInsertion C hC t W X Y Z k a (g * h) g).hom) (mul_assoc g h l).symm
  have he := HomTransport.comp_heq C.toWeaklyPointedSuperfusionData hs rfl rfl hi
    (HEq.refl (convolutionPentagonThree C hC t ht W X Y Z k))
  have hb := HomTransport.comp_heq C.toWeaklyPointedSuperfusionData hs rfl rfl
    (convolutionBlockPentagon_heq C hC t ht W X Y Z k g h l)
    (HEq.refl (convolutionFourRightInsertion C hC t W X Y Z k g h l).hom)
  have h₁ := convolutionPentagonThree_inclusion C hC t ht W X Y Z k g h l
  have h₂ := convolutionPentagonTwo_inclusion C hC t ht W X Y Z k g h l
  exact eq_of_heq (he.symm.trans ((heq_of_eq h₁).trans (hb.trans (heq_of_eq h₂.symm))))

theorem twistedPullback_pentagon (W X Y Z : (twistedPullbackData C hC t ht).Obj) :
    let D := twistedPullbackData C hC t ht
    D.comp (D.comp (D.whiskerRight (D.associatorHom W X Y) Z)
      (D.associatorHom W (D.tensorObj X Y) Z))
      (D.whiskerLeft W (D.associatorHom X Y Z)) =
    D.comp (D.associatorHom (D.tensorObj W X) Y Z) (D.associatorHom W X (D.tensorObj Y Z)) := by
  funext k
  exact convolution_pentagon C hC t ht W X Y Z k

end RMod.Classification
