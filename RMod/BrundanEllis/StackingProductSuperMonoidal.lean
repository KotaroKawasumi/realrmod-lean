import RMod.BrundanEllis.StackingProductMonoidal

/-! The raw super tensor product is a monoidal supercategory with its
component tensor and Koszul interchange. No completion or cochain comparison
is assumed in this construction. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
namespace RMod.BrundanEllis.Stacking
variable {A B : Type} [SuperCategory A] [SuperCategory B]
  [MonoidalCategory (Even A)] [MonoidalCategory (Even B)]
  [MonoidalSuperCategory A] [MonoidalSuperCategory B]

theorem productTensor_objects : TensorObjectsAgree (productTensor A B) := by
  exact fun _ _ => rfl

theorem productTensor_aligned (X X' Y Y' : Even (SuperTensorProduct A B)) :
    RMod.enrichedTensorMap SuperVec (productTensor A B) productTensor_objects X X' Y Y' =
      productTensorMap X X' Y Y' := by
  simp only [RMod.enrichedTensorMap, eqToHom_refl, Category.comp_id, Category.id_comp, productTensorMap]
  rfl

instance productEnrichedMonoidal :
    RMod.MonoidalEnrichedCategory SuperVec (SuperTensorProduct A B) where
  tensor := productTensor A B
  tensor_objects := productTensor_objects
  tensor_even f g := by
    rw [productTensor_aligned]
    simpa only [productTensorMap, ForgetEnrichment.to] using (product_tensor_homTo f g).symm
  associator_isGradedNatural := by
    apply (RMod.associator_isGradedNatural_iff SuperVec _ _).2
    intros X X' Y Y' Z Z'
    simp only [productTensor_aligned]
    simpa only [SHom, ForgetEnrichment.to, ForgetEnrichment.of] using product_associator_naturality X X' Y Y' Z Z'
  leftUnitor_isGradedNatural := by
    apply (RMod.leftUnitor_isGradedNatural_iff SuperVec _ _).2
    intros X Y
    simp only [productTensor_aligned]
    simpa only [SHom, ForgetEnrichment.to, ForgetEnrichment.of] using product_left_naturality X Y
  rightUnitor_isGradedNatural := by
    apply (RMod.rightUnitor_isGradedNatural_iff SuperVec _ _).2
    intros X Y
    simp only [productTensor_aligned]
    simpa only [SHom, ForgetEnrichment.to, ForgetEnrichment.of] using product_right_naturality X Y

instance productSuperMonoidal : MonoidalSuperCategory (SuperTensorProduct A B) :=
  Bridge.fromEnriched (SuperTensorProduct A B)

/-- The ordinary pairing has identity tensor and unit comparisons. -/
def productPairMonoidal : (productPair A B).CoreMonoidal where
  εIso := Iso.refl _
  μIso _ _ := Iso.refl _
  μIso_hom_natural_left := by
    intros X Y f Z
    have h := productPair_tensor f (𝟙 Z)
    rw [(productPair A B).map_id Z] at h
    simpa only [Iso.refl_hom, Category.comp_id, Category.id_comp, ← tensorHom_id] using h
  μIso_hom_natural_right := by
    intros X Y Z f
    have h := productPair_tensor (𝟙 Z) f
    rw [(productPair A B).map_id Z] at h
    simpa only [Iso.refl_hom, Category.comp_id, Category.id_comp, ← id_tensorHom] using h
  associativity := by
    intros
    simp only [Iso.refl_hom, id_whiskerRight, whiskerLeft_id,
      Category.id_comp, Category.comp_id]
    rfl
  left_unitality := by
    intros
    simp only [Iso.refl_hom, id_whiskerRight, Category.id_comp, Category.comp_id]
    rfl
  right_unitality := by
    intros
    simp only [Iso.refl_hom, whiskerLeft_id, Category.id_comp, Category.comp_id]
    rfl

end RMod.BrundanEllis.Stacking
