import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Removing zero summands from a biproduct

When only the j-th summand can be nonzero, its projection and inclusion
are inverse maps. Mathlib's biproduct universal property and zero-object
extensionality prove the result without selecting additional maps.
-/

set_option autoImplicit false
universe u v w

namespace RMod.Classification

open CategoryTheory CategoryTheory.Limits

noncomputable def biproductSingleIso {D : Type u} [Category.{v} D] [HasZeroMorphisms D]
    {J : Type w} (f : J → D) [HasBiproduct f] (j : J) (h : ∀ i, i ≠ j → IsZero (f i)) :
    (⨁ f) ≅ f j where
  hom := biproduct.π f j
  inv := biproduct.ι f j
  hom_inv_id := by
    apply biproduct.hom_ext
    intro i
    by_cases hi : i = j
    · subst i
      simp
    · exact (h i hi).eq_of_tgt _ _
  inv_hom_id := biproduct.ι_π_self f j

end RMod.Classification
