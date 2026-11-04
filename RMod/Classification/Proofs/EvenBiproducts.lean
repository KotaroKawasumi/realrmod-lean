import RMod.Classification.Instances.EvenBiproducts

/-!
# The chosen decomposition maps under the biproduct comparison

Mathlib's unique biproduct isomorphism carries every supplied inclusion
to the corresponding canonical inclusion and pulls its projections back
to the supplied projections. These identities fix the basis comparisons
used by all subsequent convolution expansion equations.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification.Decomposition

open CategoryTheory CategoryTheory.Limits Superfusion.Category

variable {C : WeaklyPointedSuperfusion.{u, v}} {X : LinearCategory C}
  {n : ℕ} {S : Fin n → LinearCategory C} (d : Decomposition C X S)

theorem inclusion_comparison (i : Fin n) :
    d.toEvenBicone.ι i ≫ (biproduct.uniqueUpToIso _ d.evenIsBilimit).hom =
      biproduct.ι (fun j => evenObj ℝ (LinearCategory C) (S j)) i := by
  apply biproduct.hom_ext
  intro j
  simp only [biproduct.uniqueUpToIso_hom, Category.assoc, biproduct.lift_π,
    Bicone.ι_π]

theorem comparison_projection (i : Fin n) :
    (biproduct.uniqueUpToIso _ d.evenIsBilimit).hom ≫
      biproduct.π (fun j => evenObj ℝ (LinearCategory C) (S j)) i = d.toEvenBicone.π i := by
  simp only [biproduct.uniqueUpToIso_hom, biproduct.lift_π]

theorem inclusion_comparison_inv (i : Fin n) :
    biproduct.ι (fun j => evenObj ℝ (LinearCategory C) (S j)) i ≫
      (biproduct.uniqueUpToIso _ d.evenIsBilimit).inv = d.toEvenBicone.ι i := by
  simp only [biproduct.uniqueUpToIso_inv, biproduct.ι_desc]

theorem comparison_inv_projection (i : Fin n) :
    (biproduct.uniqueUpToIso _ d.evenIsBilimit).inv ≫ d.toEvenBicone.π i =
      biproduct.π (fun j => evenObj ℝ (LinearCategory C) (S j)) i := by
  apply (cancel_epi (biproduct.uniqueUpToIso _ d.evenIsBilimit).hom).1
  rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp, comparison_projection]

end RMod.Classification.Decomposition
