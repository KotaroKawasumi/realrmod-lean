import RMod.Classification.Instances.ConvolutionFourInsertions
import RMod.Classification.Proofs.ConvolutionMappedExt
import RMod.Classification.Proofs.FunctorComposition

/-!
# Fourfold inclusions detect equality

Apply the threefold summand test after tensoring by the fourth object
and its prescribed parity factor. Both tensor functors act on the full
Hom spaces. Multiplicative reparametrization then expresses the left
summands by the individual degrees g, h and l used in the pentagon.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData)

theorem hom_ext_of_convolutionFourLeftInsertions (W X Y Z : PullbackObj C t) (k : t.group)
    {M : C.Obj}
    {f g : C.Hom (convolutionObj C hC t (convolutionObj C hC t (convolutionObj C hC t W X) Y) Z k).val M}
    (he : ∀ a b c, C.comp (convolutionFourLeftInsertion C hC t W X Y Z k a b c).hom f =
      C.comp (convolutionFourLeftInsertion C hC t W X Y Z k a b c).hom g) : f = g := by
  apply hom_ext_of_convolutionInclusions C hC t (convolutionObj C hC t (convolutionObj C hC t W X) Y) Z k
  intro a
  let A : WeaklyPointedSuperfusion := ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩
  let F₁ := tensorRightSuperfunctor A (Z (a⁻¹ * k)).val
  let F₂ := tensorRightSuperfunctor A (C.pi.factor (t.nu a (a⁻¹ * k)))
  let F : Superfunctor A A := ⟨F₁.data.comp F₂.data, F₁.laws.compose F₂.laws⟩
  apply hom_ext_of_mapped_convolutionLeftInsertions C hC t A F W X Y a
  intro b c
  have hi := he a b c
  change C.comp (C.comp (F.data.map (convolutionLeftInsertionEven C hC t W X Y a b c).hom)
    (convolutionInclusion C hC t (convolutionObj C hC t (convolutionObj C hC t W X) Y) Z k a)) f =
    C.comp (C.comp (F.data.map (convolutionLeftInsertionEven C hC t W X Y a b c).hom)
      (convolutionInclusion C hC t (convolutionObj C hC t (convolutionObj C hC t W X) Y) Z k a)) g at hi
  simp only [hC.comp_assoc] at hi
  exact hi

theorem hom_ext_of_convolutionFourRightInsertions (W X Y Z : PullbackObj C t) (k : t.group)
    {M : C.Obj}
    {f g : C.Hom (convolutionObj C hC t W (convolutionObj C hC t X (convolutionObj C hC t Y Z)) k).val M}
    (he : ∀ a b c, C.comp (convolutionFourRightInsertion C hC t W X Y Z k a b c).hom f =
      C.comp (convolutionFourRightInsertion C hC t W X Y Z k a b c).hom g) : f = g := by
  apply hom_ext_of_convolutionInclusions C hC t W (convolutionObj C hC t X (convolutionObj C hC t Y Z)) k
  intro a
  let A : WeaklyPointedSuperfusion := ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩
  let F₁ := tensorLeftSuperfunctor A (W a).val
  let F₂ := tensorRightSuperfunctor A (C.pi.factor (t.nu a (a⁻¹ * k)))
  let F : Superfunctor A A := ⟨F₁.data.comp F₂.data, F₁.laws.compose F₂.laws⟩
  apply hom_ext_of_mapped_convolutionRightInsertions C hC t A F X Y Z (a⁻¹ * k)
  intro b c
  have hi := he a b c
  change C.comp (C.comp (F.data.map (convolutionRightInsertionEven C hC t X Y Z (a⁻¹ * k) b c).hom)
    (convolutionInclusion C hC t W (convolutionObj C hC t X (convolutionObj C hC t Y Z)) k a)) f =
    C.comp (C.comp (F.data.map (convolutionRightInsertionEven C hC t X Y Z (a⁻¹ * k) b c).hom)
      (convolutionInclusion C hC t W (convolutionObj C hC t X (convolutionObj C hC t Y Z)) k a)) g at hi
  simp only [hC.comp_assoc] at hi
  exact hi

theorem hom_ext_of_convolutionFourLeftInsertions_degrees (W X Y Z : PullbackObj C t) (k : t.group)
    {M : C.Obj}
    {f g : C.Hom (convolutionObj C hC t (convolutionObj C hC t (convolutionObj C hC t W X) Y) Z k).val M}
    (he : ∀ a b c,
      C.comp (convolutionFourLeftInsertion C hC t W X Y Z k ((a * b) * c) (a * b) a).hom f =
        C.comp (convolutionFourLeftInsertion C hC t W X Y Z k ((a * b) * c) (a * b) a).hom g) : f = g := by
  apply hom_ext_of_convolutionFourLeftInsertions C hC t W X Y Z k
  intro a b c
  let P : t.group → t.group → Prop := fun a' b' =>
    C.comp (convolutionFourLeftInsertion C hC t W X Y Z k a' b' c).hom f =
      C.comp (convolutionFourLeftInsertion C hC t W X Y Z k a' b' c).hom g
  have h₁ : (c * (c⁻¹ * b)) * (b⁻¹ * a) = a := by rw [mul_inv_cancel_left, mul_inv_cancel_left]
  have h₂ : c * (c⁻¹ * b) = b := mul_inv_cancel_left c b
  exact Eq.mp (congrArg₂ P h₁ h₂) (he c (c⁻¹ * b) (b⁻¹ * a))

end RMod.Classification
