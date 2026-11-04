import RMod.Classification.Instances.Decomposition
import RMod.Classification.Instances.LinearMonoidal
import Superfusion.Category.Even
import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Mathlib finite biproducts in the even category

The selected even inclusions and projections give a Mathlib bicone.
Its total identity supplies the bilimit through Mathlib's preadditive
criterion. This makes Mathlib's reindexing, iterated-biproduct and monoidal
distributivity isomorphisms available with even underlying maps.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification

open CategoryTheory CategoryTheory.Limits Superfusion.Category

namespace Decomposition

variable {C : WeaklyPointedSuperfusion.{u, v}} {X : LinearCategory C}
  {n : ℕ} {S : Fin n → LinearCategory C} (d : Decomposition C X S)

/-- The existing even-category adapter uses the noncomputable real-field
instance. The underlying inclusion and projection maps are unchanged. -/
noncomputable def toEvenBicone : Bicone (fun i => evenObj ℝ (LinearCategory C) (S i)) where
  pt := evenObj ℝ (LinearCategory C) X
  π i := ⟨d.data.projection i, d.laws.projection_even i⟩
  ι i := ⟨d.data.inclusion i, d.laws.inclusion_even i⟩
  ι_π i j := by
    by_cases h : i = j
    · subst j
      simp only [dite_true, eqToHom_refl]
      apply WideSubcategory.hom_ext
      exact d.laws.diagonal i
    · rw [dif_neg h]
      apply WideSubcategory.hom_ext
      exact d.laws.off_diagonal i j h

noncomputable def evenIsBilimit : d.toEvenBicone.IsBilimit := by
  apply isBilimitOfTotal
  apply WideSubcategory.hom_ext
  have ht := d.laws.total
  rw [LinearCategory.finSum_eq_sum C] at ht
  have hm := (wideSubcategoryInclusion (evenMorphismProperty ℝ (LinearCategory C))).map_sum
    (fun i => d.toEvenBicone.π i ≫ d.toEvenBicone.ι i) Finset.univ
  exact hm.trans ht

end Decomposition

namespace LinearCategory

variable (C : WeaklyPointedSuperfusion.{u, v})

instance evenHasFiniteBiproducts : HasFiniteBiproducts (EvenSubcategory ℝ (LinearCategory C)) where
  out n := ⟨fun S => by
    obtain ⟨X, hX⟩ := C.laws.has_finite_biproducts (fun i => (S i).obj)
    obtain ⟨d⟩ := (hasDecomposition_iff C X (fun i => (S i).obj)).mp hX
    exact HasBiproduct.mk ⟨d.toEvenBicone, d.evenIsBilimit⟩⟩

end LinearCategory
end RMod.Classification
