import RMod.Classification.Proofs.ConvolutionFourExt
import RMod.Classification.Proofs.ConvolutionNaturality

/-!
The only parameter law used in this file is the parity cocycle.
No scalar normalization or pentagon for omega is assumed.

# The two whiskered edges of the fourfold pentagon

For the first and last edges of the long path, a fixed-object tensor
functor carries the exact threefold associator insertion equation to the
fourfold one. The outer convolution map commutes with its inclusion.
-/

set_option autoImplicit false

namespace RMod.Classification

attribute [local implicit_reducible] convolutionFourLeftFamily convolutionFourInnerFamily
  convolutionFourOuterFamily convolutionFourRightFamily convolutionLeftFamily
  convolutionRightFamily convolutionEvenFamily twistSummand

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData)
  (hν : ∀ g h k : t.group, t.nu g h + t.nu (g * h) k = t.nu h k + t.nu g (h * k))

theorem convolutionFourLeftInsertion_firstOfParity (W X Y Z : PullbackObj C t) (k a b c : t.group) :
    C.comp (convolutionFourLeftInsertion C hC t W X Y Z k a (b * c) b).hom
      (convolutionHom C hC t (fun g => (convolutionAssociatorDataOfParity C hC t hν W X Y g).hom)
        (fun g => C.id (Z g).val) k) =
    C.comp (C.tensorHom (C.tensorHom (convolutionBlockIsoOfParity C hC t hν W X Y a b c).hom.hom
      (C.id (Z (a⁻¹ * k)).val)) (C.id (C.pi.factor (t.nu a (a⁻¹ * k)))))
      (convolutionFourInnerInsertion C hC t W X Y Z k a b c).hom := by
  let A : WeaklyPointedSuperfusion := ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩
  let F₁ := tensorRightSuperfunctor A (Z (a⁻¹ * k)).val
  let F₂ := tensorRightSuperfunctor A (C.pi.factor (t.nu a (a⁻¹ * k)))
  let F : Superfunctor A A := ⟨F₁.data.comp F₂.data, F₁.laws.compose F₂.laws⟩
  change C.comp (C.comp (F.data.map (convolutionLeftInsertionEven C hC t W X Y a (b * c) b).hom)
    (convolutionInclusion C hC t (convolutionObj C hC t (convolutionObj C hC t W X) Y) Z k a)) _ =
    C.comp (F.data.map (convolutionBlockIsoOfParity C hC t hν W X Y a b c).hom.hom)
      (C.comp (F.data.map (convolutionRightInsertionEven C hC t W X Y a b c).hom)
        (convolutionInclusion C hC t (convolutionObj C hC t W (convolutionObj C hC t X Y)) Z k a))
  erw [hC.comp_assoc, convolutionInclusion_map]
  change C.comp (F.data.map (convolutionLeftInsertionEven C hC t W X Y a (b * c) b).hom)
    (C.comp (F.data.map (convolutionAssociatorDataOfParity C hC t hν W X Y a).hom)
      (convolutionInclusion C hC t (convolutionObj C hC t W (convolutionObj C hC t X Y)) Z k a)) = _
  erw [← hC.comp_assoc, ← F.laws.map_comp, convolutionAssociatorOfParity_inclusion_hom,
    F.laws.map_comp, hC.comp_assoc]

theorem convolutionFourOuterInsertion_lastOfParity (W X Y Z : PullbackObj C t) (k a b c : t.group) :
    C.comp (convolutionFourOuterInsertion C hC t W X Y Z k a (b * c) b).hom
      (convolutionHom C hC t (fun g => C.id (W g).val)
        (fun g => (convolutionAssociatorDataOfParity C hC t hν X Y Z g).hom) k) =
    C.comp (C.tensorHom (C.tensorHom (C.id (W a).val)
      (convolutionBlockIsoOfParity C hC t hν X Y Z (a⁻¹ * k) b c).hom.hom)
      (C.id (C.pi.factor (t.nu a (a⁻¹ * k)))))
      (convolutionFourRightInsertion C hC t W X Y Z k a b c).hom := by
  let A : WeaklyPointedSuperfusion := ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩
  let F₁ := tensorLeftSuperfunctor A (W a).val
  let F₂ := tensorRightSuperfunctor A (C.pi.factor (t.nu a (a⁻¹ * k)))
  let F : Superfunctor A A := ⟨F₁.data.comp F₂.data, F₁.laws.compose F₂.laws⟩
  change C.comp (C.comp (F.data.map (convolutionLeftInsertionEven C hC t X Y Z (a⁻¹ * k) (b * c) b).hom)
    (convolutionInclusion C hC t W (convolutionObj C hC t (convolutionObj C hC t X Y) Z) k a)) _ =
    C.comp (F.data.map (convolutionBlockIsoOfParity C hC t hν X Y Z (a⁻¹ * k) b c).hom.hom)
      (C.comp (F.data.map (convolutionRightInsertionEven C hC t X Y Z (a⁻¹ * k) b c).hom)
        (convolutionInclusion C hC t W (convolutionObj C hC t X (convolutionObj C hC t Y Z)) k a))
  erw [hC.comp_assoc, convolutionInclusion_map]
  change C.comp (F.data.map (convolutionLeftInsertionEven C hC t X Y Z (a⁻¹ * k) (b * c) b).hom)
    (C.comp (F.data.map (convolutionAssociatorDataOfParity C hC t hν X Y Z (a⁻¹ * k)).hom)
      (convolutionInclusion C hC t W (convolutionObj C hC t X (convolutionObj C hC t Y Z)) k a)) = _
  erw [← hC.comp_assoc, ← F.laws.map_comp, convolutionAssociatorOfParity_inclusion_hom,
    F.laws.map_comp, hC.comp_assoc]

end RMod.Classification
