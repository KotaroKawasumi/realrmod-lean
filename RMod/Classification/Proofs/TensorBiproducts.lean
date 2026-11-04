import Mathlib.CategoryTheory.Monoidal.Preadditive

/-!
# Tensor distributors on transported biproduct inclusions

These equations retain an arbitrary chosen sum object through its
comparison isomorphism. They let the two distributors in a convolution
expansion cancel that comparison on each individual summand.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification

open CategoryTheory CategoryTheory.Limits MonoidalCategory

variable {V : Type u} [Category.{v} V] [Preadditive V] [MonoidalCategory V]
  [MonoidalPreadditive V] [HasFiniteBiproducts V]
  {J : Type} [Finite J] (F : J → V) {S : V} (e : S ≅ ⨁ F) (W P : V)

theorem rightTensorExpansion_inclusion (j : J) :
    ((biproduct.ι F j ≫ e.inv) ▷ W) ▷ P ≫ (e.hom ▷ W) ▷ P ≫
      (rightDistributor F W).hom ▷ P ≫ (rightDistributor (fun j => F j ⊗ W) P).hom =
        biproduct.ι (fun j => (F j ⊗ W) ⊗ P) j := by
  simp only [← comp_whiskerRight_assoc, Category.assoc,
    Iso.inv_hom_id, Category.comp_id, biproduct_ι_comp_rightDistributor_hom]

theorem leftTensorExpansion_inclusion (j : J) :
    (W ◁ (biproduct.ι F j ≫ e.inv)) ▷ P ≫ (W ◁ e.hom) ▷ P ≫
      (leftDistributor W F).hom ▷ P ≫ (rightDistributor (fun j => W ⊗ F j) P).hom =
        biproduct.ι (fun j => (W ⊗ F j) ⊗ P) j := by
  simp only [← comp_whiskerRight_assoc, ← whiskerLeft_comp_assoc,
    Category.assoc, Iso.inv_hom_id, Category.comp_id,
    biproduct_ι_comp_leftDistributor_hom, biproduct_ι_comp_rightDistributor_hom]

end RMod.Classification
