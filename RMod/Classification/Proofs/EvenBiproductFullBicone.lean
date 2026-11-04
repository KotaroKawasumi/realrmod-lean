import RMod.Classification.Instances.EvenBiproductFullBicone

/-!
# Even biproduct coordinates detect every morphism

The total matrix identity survives the additive inclusion functor.
Mathlib's preadditive criterion then supplies both universal properties
in the full category, with the originally chosen even structural maps.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory CategoryTheory.Limits Superfusion.Category

variable (C : WeaklyPointedSuperfusion.{0, 0}) {I : Type} [Fintype I]

noncomputable def evenBiproductFullIsBilimit (V : I → EvenSubcategory ℝ (LinearCategory C)) :
    (evenBiproductFullBicone C V).IsBilimit := by
  apply isBilimitOfTotal
  let F := wideSubcategoryInclusion (evenMorphismProperty ℝ (LinearCategory C))
  change (∑ i, F.map (biproduct.π V i) ≫ F.map (biproduct.ι V i)) = 𝟙 _
  simp only [← F.map_comp, ← F.map_sum, biproduct.total, F.map_id]

end RMod.Classification
