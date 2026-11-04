import RMod.Enriched.Surface
import RMod.BrundanEllis.StackingSymmetricInterchange

/-! Exchange the two enriched factors using the given symmetry of the base.
The functor laws retain the Koszul interchange in every homogeneous degree. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.BraidedCategory
namespace RMod.BrundanEllis.Stacking
universe u₁ u₂ v w
variable (V : Type v) [Category.{w} V] [MonoidalCategory V] [SymmetricCategory V]
  (C : Type u₁) (D : Type u₂) [EnrichedCategory V C] [EnrichedCategory V D]

def enrichedSwap : EnrichedFunctor V (EnrichedTensorProduct V C D) (EnrichedTensorProduct V D C) where
  obj X := EnrichedTensorProduct.of V X.2 X.1
  map X Y := (β_ (X.1 ⟶[V] Y.1) (X.2 ⟶[V] Y.2)).hom
  map_id X := by
    change ((λ_ (𝟙_ V)).inv ≫ (eId V X.1 ⊗ₘ eId V X.2)) ≫ (β_ _ _).hom =
      (λ_ (𝟙_ V)).inv ≫ (eId V X.2 ⊗ₘ eId V X.1)
    rw [Category.assoc, braiding_naturality, ← Category.assoc, leftUnitor_inv_braiding]
    monoidal
  map_comp X Y Z := by
    change (tensorμ _ _ _ _ ≫ (eComp V X.1 Y.1 Z.1 ⊗ₘ eComp V X.2 Y.2 Z.2)) ≫
      (β_ _ _).hom = ((β_ _ _).hom ⊗ₘ (β_ _ _).hom) ≫
        tensorμ _ _ _ _ ≫ (eComp V X.2 Y.2 Z.2 ⊗ₘ eComp V X.1 Y.1 Z.1)
    rw [Category.assoc, braiding_naturality, ← Category.assoc, tensorMu_swap, Category.assoc]

end RMod.BrundanEllis.Stacking
