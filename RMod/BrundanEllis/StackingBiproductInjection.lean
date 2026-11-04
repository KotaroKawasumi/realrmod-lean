import Mathlib.CategoryTheory.Limits.Shapes.Biproducts

/-! Extending a finite biproduct by zero summands changes none of its
objects up to the canonical inclusion/projection isomorphism. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 60000
open CategoryTheory CategoryTheory.Limits CategoryTheory.Category
namespace RMod.BrundanEllis.Stacking
variable {C I J : Type} [Category C] [HasZeroMorphisms C]
  (X : I → C) (e : J ↪ I) [HasBiproduct X] [HasBiproduct (fun j => X (e j))]

/-- Inclusion of the image-indexed summands is invertible when all others vanish. -/
def biproductInjectionIso (hz : ∀ i, (¬ ∃ j, e j = i) → IsZero (X i)) :
    (⨁ fun j => X (e j)) ≅ ⨁ X where
  hom := biproduct.desc (fun j => biproduct.ι X (e j))
  inv := biproduct.lift (fun j => biproduct.π X (e j))
  hom_inv_id := by
    classical
    ext i j
    simp [biproduct.ι_π, e.injective.eq_iff]
  inv_hom_id := by
    classical
    apply biproduct.hom_ext'
    intro i
    by_cases hi : ∃ j, e j = i
    · obtain ⟨j, rfl⟩ := hi
      have h : biproduct.ι X (e j) ≫ biproduct.lift (fun k => biproduct.π X (e k)) =
          biproduct.ι (fun k => X (e k)) j := by
        ext k
        simp [biproduct.ι_π, e.injective.eq_iff]
      rw [← assoc, h, biproduct.ι_desc, Category.comp_id]
    · exact (hz i hi).eq_of_src _ _

@[reassoc] theorem biproductInjectionIso_inclusion
    (hz : ∀ i, (¬ ∃ j, e j = i) → IsZero (X i)) (j : J) :
    biproduct.ι (fun j => X (e j)) j ≫ (biproductInjectionIso X e hz).hom =
      biproduct.ι X (e j) := biproduct.ι_desc _ _

@[reassoc] theorem biproductInjectionIso_projection
    (hz : ∀ i, (¬ ∃ j, e j = i) → IsZero (X i)) (j : J) :
    (biproductInjectionIso X e hz).inv ≫ biproduct.π (fun j => X (e j)) j =
      biproduct.π X (e j) := biproduct.lift_π _ _

end RMod.BrundanEllis.Stacking
