import RMod.Classification.Instances.EvenBiproducts

/-!
# The chosen even biproduct as a bicone in the full category

Forget the evenness proofs on the chosen structural maps. Mathlib's
bicone functoriality retains the same object, inclusions and projections.
The next proof establishes universality also for odd and mixed maps.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory CategoryTheory.Limits Superfusion.Category

variable (C : WeaklyPointedSuperfusion.{0, 0}) {I : Type} [Fintype I]

noncomputable def evenBiproductFullBicone (V : I → EvenSubcategory ℝ (LinearCategory C)) :
    Bicone (C := LinearCategory C) (fun i => (V i).obj) :=
  (Bicones.functoriality V (wideSubcategoryInclusion (evenMorphismProperty ℝ (LinearCategory C)))).obj
    (biproduct.bicone V)

end RMod.Classification
