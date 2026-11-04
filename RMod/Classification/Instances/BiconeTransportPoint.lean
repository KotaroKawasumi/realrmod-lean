import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Moving a biproduct presentation along a specified isomorphism

The point changes, while every inclusion and projection is explicitly
composed with the given isomorphism. No new choice of a presentation is
made. Universality is a separate result for these exact maps.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory CategoryTheory.Limits

variable {C : Type*} [Category C] [Preadditive C] {I : Type*} {V : I → C}

def biconeTransportPoint (b : Bicone V) {X : C} (e : b.pt ≅ X) : Bicone V where
  pt := X
  π i := e.inv ≫ b.π i
  ι i := b.ι i ≫ e.hom
  ι_π i j := by
    simp only [Category.assoc, e.hom_inv_id_assoc, b.ι_π]

end RMod.Classification
