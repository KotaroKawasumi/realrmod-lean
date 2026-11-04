import RMod.Classification.Proofs.ConvolutionBlocks
import RMod.Classification.Proofs.ConvolutionBlockNaturality
import RMod.Classification.Proofs.ConvolutionTripleMaps
import RMod.Classification.Proofs.ConvolutionTripleExt
import RMod.Classification.Instances.TwistedPullbackData

/-!
# Naturality of the actual convolution associator

Threefold inclusions detect equality on the entire graded Hom space.
On each summand, the two sides are the previously established local
normalizer square. The biproduct comparisons therefore introduce no
additional naturality assumptions.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData)
  (ht : TwistLaws t)

theorem convolutionAssociator_inclusion_hom (X Y Z : PullbackObj C t) (k a b : t.group) :
    C.comp (convolutionLeftInsertionEven C hC t X Y Z k (a * b) a).hom
      (convolutionAssociatorData C hC t ht X Y Z k).hom =
        C.comp (convolutionBlockIso C hC t ht X Y Z k a b).hom.hom
          (convolutionRightInsertionEven C hC t X Y Z k a b).hom :=
  congrArg (fun f => f.hom) (convolutionAssociator_inclusion C hC t ht X Y Z k a b)

/-- Multiplication reparametrizes the two free summand indices. -/
theorem hom_ext_of_convolutionLeftInsertions_pairs (X Y Z : PullbackObj C t) (k : t.group)
    {M : C.Obj} {f g : C.Hom (convolutionObj C hC t (convolutionObj C hC t X Y) Z k).val M}
    (he : ∀ a b, C.comp (convolutionLeftInsertionEven C hC t X Y Z k (a * b) a).hom f =
      C.comp (convolutionLeftInsertionEven C hC t X Y Z k (a * b) a).hom g) : f = g := by
  apply hom_ext_of_convolutionLeftInsertions C hC t X Y Z k
  intro a b
  let P : t.group → Prop := fun c =>
    C.comp (convolutionLeftInsertionEven C hC t X Y Z k c b).hom f =
      C.comp (convolutionLeftInsertionEven C hC t X Y Z k c b).hom g
  exact Eq.mp (congrArg P (mul_inv_cancel_left b a)) (he b (b⁻¹ * a))

theorem convolutionAssociatorOfParity_naturality
    (hν : ∀ g h k : t.group, t.nu g h + t.nu (g * h) k = t.nu h k + t.nu g (h * k))
    {X X' Y Y' Z Z' : PullbackObj C t}
    (f : PullbackHom C t X X') (g : PullbackHom C t Y Y') (h : PullbackHom C t Z Z')
    (k : t.group) :
    C.comp (convolutionHom C hC t (convolutionHom C hC t f g) h k)
      (convolutionAssociatorDataOfParity C hC t hν X' Y' Z' k).hom =
        C.comp (convolutionAssociatorDataOfParity C hC t hν X Y Z k).hom
          (convolutionHom C hC t f (convolutionHom C hC t g h) k) := by
  apply hom_ext_of_convolutionLeftInsertions_pairs C hC t X Y Z k
  intro a b
  rw [← hC.comp_assoc, convolutionLeftInsertion_map, hC.comp_assoc,
    convolutionAssociatorOfParity_inclusion_hom, ← hC.comp_assoc, convolutionBlockIsoOfParity_naturality,
    hC.comp_assoc, ← convolutionRightInsertion_map, ← hC.comp_assoc,
    ← convolutionAssociatorOfParity_inclusion_hom, hC.comp_assoc]

theorem convolutionAssociator_naturality {X X' Y Y' Z Z' : PullbackObj C t}
    (f : PullbackHom C t X X') (g : PullbackHom C t Y Y') (h : PullbackHom C t Z Z')
    (k : t.group) :
    C.comp (convolutionHom C hC t (convolutionHom C hC t f g) h k)
      (convolutionAssociatorData C hC t ht X' Y' Z' k).hom =
        C.comp (convolutionAssociatorData C hC t ht X Y Z k).hom
          (convolutionHom C hC t f (convolutionHom C hC t g h) k) :=
  convolutionAssociatorOfParity_naturality C hC t ht.normalizer_parity f g h k

theorem twistedPullback_associator_naturality
    {X₁ X₂ X₃ Y₁ Y₂ Y₃ : (twistedPullbackData C hC t ht).Obj}
    (f₁ : (twistedPullbackData C hC t ht).Hom X₁ Y₁)
    (f₂ : (twistedPullbackData C hC t ht).Hom X₂ Y₂)
    (f₃ : (twistedPullbackData C hC t ht).Hom X₃ Y₃) :
    let D := twistedPullbackData C hC t ht
    D.comp (D.tensorHom (D.tensorHom f₁ f₂) f₃) (D.associatorHom Y₁ Y₂ Y₃) =
      D.comp (D.associatorHom X₁ X₂ X₃) (D.tensorHom f₁ (D.tensorHom f₂ f₃)) := by
  funext k
  exact convolutionAssociator_naturality C hC t ht f₁ f₂ f₃ k

end RMod.Classification
