import RMod.Classification.Instances.ConvolutionSummandFamilies
import RMod.Classification.Proofs.ConvolutionFourExt
import RMod.Classification.Proofs.ConvolutionTripleMaps
import RMod.Classification.Proofs.ConvolutionMaps

/-!
# Fourfold inclusions as images of threefold inclusions

Replace one adjacent pair by its fixed-degree summand family. Mapping
that family into its convolution recovers the selected fourfold
inclusion. These factorizations let the already proved naturality of the
actual associator control the three non-whiskered pentagon edges.
-/

set_option autoImplicit false

namespace RMod.Classification

attribute [local implicit_reducible] convolutionFourLeftFamily convolutionFourInnerFamily
  convolutionFourMiddleFamily convolutionFourOuterFamily convolutionFourRightFamily
  convolutionLeftFamily convolutionRightFamily convolutionEvenFamily twistSummand convolutionSummandObj

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData)

theorem convolutionFourLeft_factor (W X Y Z : PullbackObj C t) (k a b c : t.group) :
    C.comp (convolutionLeftInsertionEven C hC t (convolutionSummandObj C hC t W X c) Y Z k a b).hom
      (convolutionHom C hC t
        (convolutionHom C hC t (convolutionSummandInclusion C hC t W X c) (fun g => C.id (Y g).val))
        (fun g => C.id (Z g).val) k) =
      (convolutionFourLeftInsertion C hC t W X Y Z k a b c).hom := by
  erw [convolutionLeftInsertion_map]
  let A : WeaklyPointedSuperfusion := ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩
  let F₁ := tensorRightSuperfunctor A (Z (a⁻¹ * k)).val
  let F₂ := tensorRightSuperfunctor A (C.pi.factor (t.nu a (a⁻¹ * k)))
  let F : Superfunctor A A := ⟨F₁.data.comp F₂.data, F₁.laws.compose F₂.laws⟩
  let i := C.tensorHom (C.tensorHom (convolutionInclusion C hC t W X b c)
    (C.id (Y (b⁻¹ * a)).val)) (C.id (C.pi.factor (t.nu b (b⁻¹ * a))))
  let j := convolutionInclusion C hC t (convolutionObj C hC t W X) Y a b
  let q := convolutionInclusion C hC t (convolutionObj C hC t (convolutionObj C hC t W X) Y) Z k a
  change C.comp (F.data.map i) (C.comp (F.data.map j) q) = C.comp (F.data.map (C.comp i j)) q
  erw [← hC.comp_assoc, ← F.laws.map_comp]

theorem convolutionFourInner_factor (W X Y Z : PullbackObj C t) (k a b c : t.group) :
    C.comp (convolutionLeftInsertionEven C hC t W (convolutionSummandObj C hC t X Y c) Z k a b).hom
      (convolutionHom C hC t
        (convolutionHom C hC t (fun g => C.id (W g).val) (convolutionSummandInclusion C hC t X Y c))
        (fun g => C.id (Z g).val) k) =
      (convolutionFourInnerInsertion C hC t W X Y Z k a b c).hom := by
  erw [convolutionLeftInsertion_map]
  let A : WeaklyPointedSuperfusion := ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩
  let F₁ := tensorRightSuperfunctor A (Z (a⁻¹ * k)).val
  let F₂ := tensorRightSuperfunctor A (C.pi.factor (t.nu a (a⁻¹ * k)))
  let F : Superfunctor A A := ⟨F₁.data.comp F₂.data, F₁.laws.compose F₂.laws⟩
  let i := C.tensorHom (C.tensorHom (C.id (W b).val)
    (convolutionInclusion C hC t X Y (b⁻¹ * a) c)) (C.id (C.pi.factor (t.nu b (b⁻¹ * a))))
  let j := convolutionInclusion C hC t W (convolutionObj C hC t X Y) a b
  let q := convolutionInclusion C hC t (convolutionObj C hC t W (convolutionObj C hC t X Y)) Z k a
  change C.comp (F.data.map i) (C.comp (F.data.map j) q) = C.comp (F.data.map (C.comp i j)) q
  erw [← hC.comp_assoc, ← F.laws.map_comp]

theorem convolutionFourOuter_factor (W X Y Z : PullbackObj C t) (k a b c : t.group) :
    C.comp (convolutionRightInsertionEven C hC t W (convolutionSummandObj C hC t X Y c) Z k a b).hom
      (convolutionHom C hC t (fun g => C.id (W g).val)
        (convolutionHom C hC t (convolutionSummandInclusion C hC t X Y c) (fun g => C.id (Z g).val)) k) =
      (convolutionFourOuterInsertion C hC t W X Y Z k a b c).hom := by
  erw [convolutionRightInsertion_map]
  let A : WeaklyPointedSuperfusion := ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩
  let F₁ := tensorLeftSuperfunctor A (W a).val
  let F₂ := tensorRightSuperfunctor A (C.pi.factor (t.nu a (a⁻¹ * k)))
  let F : Superfunctor A A := ⟨F₁.data.comp F₂.data, F₁.laws.compose F₂.laws⟩
  let i := C.tensorHom (C.tensorHom (convolutionInclusion C hC t X Y b c)
    (C.id (Z (b⁻¹ * (a⁻¹ * k))).val)) (C.id (C.pi.factor (t.nu b (b⁻¹ * (a⁻¹ * k)))))
  let j := convolutionInclusion C hC t (convolutionObj C hC t X Y) Z (a⁻¹ * k) b
  let q := convolutionInclusion C hC t W (convolutionObj C hC t (convolutionObj C hC t X Y) Z) k a
  change C.comp (F.data.map i) (C.comp (F.data.map j) q) = C.comp (F.data.map (C.comp i j)) q
  erw [← hC.comp_assoc, ← F.laws.map_comp]

theorem convolutionFourRight_factor (W X Y Z : PullbackObj C t) (k a b c : t.group) :
    C.comp (convolutionRightInsertionEven C hC t W X (convolutionSummandObj C hC t Y Z c) k a b).hom
      (convolutionHom C hC t (fun g => C.id (W g).val)
        (convolutionHom C hC t (fun g => C.id (X g).val) (convolutionSummandInclusion C hC t Y Z c)) k) =
      (convolutionFourRightInsertion C hC t W X Y Z k a b c).hom := by
  erw [convolutionRightInsertion_map]
  let A : WeaklyPointedSuperfusion := ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩
  let F₁ := tensorLeftSuperfunctor A (W a).val
  let F₂ := tensorRightSuperfunctor A (C.pi.factor (t.nu a (a⁻¹ * k)))
  let F : Superfunctor A A := ⟨F₁.data.comp F₂.data, F₁.laws.compose F₂.laws⟩
  let i := C.tensorHom (C.tensorHom (C.id (X b).val)
    (convolutionInclusion C hC t Y Z (b⁻¹ * (a⁻¹ * k)) c))
    (C.id (C.pi.factor (t.nu b (b⁻¹ * (a⁻¹ * k)))))
  let j := convolutionInclusion C hC t X (convolutionObj C hC t Y Z) (a⁻¹ * k) b
  let q := convolutionInclusion C hC t W (convolutionObj C hC t X (convolutionObj C hC t Y Z)) k a
  change C.comp (F.data.map i) (C.comp (F.data.map j) q) = C.comp (F.data.map (C.comp i j)) q
  erw [← hC.comp_assoc, ← F.laws.map_comp]

theorem convolutionFourMiddle_factor_first (W X Y Z : PullbackObj C t) (k a b c : t.group) :
    C.comp (convolutionRightInsertionEven C hC t (convolutionSummandObj C hC t W X c) Y Z k a b).hom
      (convolutionHom C hC t (convolutionSummandInclusion C hC t W X c)
        (convolutionHom C hC t (fun g => C.id (Y g).val) (fun g => C.id (Z g).val)) k) =
      (convolutionFourMiddleInsertion C hC t W X Y Z k a c b).hom := by
  erw [convolutionRightInsertion_map]
  simp only [convolutionRightBlockHom, twistSummandHom_id C hC.toWeaklyPointedSuperfusionLaws]
  let i := convolutionInclusion C hC t W X a c
  let j := convolutionInclusion C hC t Y Z (a⁻¹ * k) b
  let P := C.pi.factor (t.nu a (a⁻¹ * k))
  let q := convolutionInclusion C hC t (convolutionObj C hC t W X) (convolutionObj C hC t Y Z) k a
  change C.comp (C.tensorHom (C.tensorHom i (C.id (twistSummand C t Y Z b (b⁻¹ * (a⁻¹ * k))))) (C.id P))
    (C.comp (C.tensorHom (C.tensorHom (C.id (convolutionObj C hC t W X a).val) j) (C.id P)) q) =
      C.comp (C.tensorHom (C.tensorHom i j) (C.id P)) q
  erw [← hC.comp_assoc, interchange_second_even hC.toWeaklyPointedSuperfusionLaws _ _ _ _ (hC.id_even _),
    hC.comp_id, interchange_first_even hC.toWeaklyPointedSuperfusionLaws _ _ _ _
      (convolutionInclusion_grade C hC t W X a c), hC.comp_id, hC.id_comp]

theorem convolutionFourMiddle_factor_last (W X Y Z : PullbackObj C t) (k a b c : t.group) :
    C.comp (convolutionLeftInsertionEven C hC t W X (convolutionSummandObj C hC t Y Z c) k a b).hom
      (convolutionHom C hC t
        (convolutionHom C hC t (fun g => C.id (W g).val) (fun g => C.id (X g).val))
        (convolutionSummandInclusion C hC t Y Z c) k) =
      (convolutionFourMiddleInsertion C hC t W X Y Z k a b c).hom := by
  erw [convolutionLeftInsertion_map]
  simp only [convolutionLeftBlockHom, twistSummandHom_id C hC.toWeaklyPointedSuperfusionLaws]
  let i := convolutionInclusion C hC t W X a b
  let j := convolutionInclusion C hC t Y Z (a⁻¹ * k) c
  let P := C.pi.factor (t.nu a (a⁻¹ * k))
  let q := convolutionInclusion C hC t (convolutionObj C hC t W X) (convolutionObj C hC t Y Z) k a
  change C.comp (C.tensorHom (C.tensorHom (C.id (twistSummand C t W X b (b⁻¹ * a))) j) (C.id P))
    (C.comp (C.tensorHom (C.tensorHom i (C.id (convolutionObj C hC t Y Z (a⁻¹ * k)).val)) (C.id P)) q) =
      C.comp (C.tensorHom (C.tensorHom i j) (C.id P)) q
  erw [← hC.comp_assoc, interchange_second_even hC.toWeaklyPointedSuperfusionLaws _ _ _ _ (hC.id_even _),
    hC.comp_id, interchange_first_even hC.toWeaklyPointedSuperfusionLaws _ _ _ _ (hC.id_even _),
    hC.id_comp, hC.comp_id]

end RMod.Classification
