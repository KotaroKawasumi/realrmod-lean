import RMod.Classification.Proofs.IndexedFullSubcategoryFunctor

/-!
# Index equality for maps to a varying component object

The source object has presentations in two equal components; the target
and its incoming map belong to a specified component-indexed family.
Equality of indices transports both component images and their maps.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

theorem indexedFullSubcategoryFunctor_family_naturality
    {C D : Type*} [Category C] [Category D] {I : Type*}
    (P : I → ObjectProperty C) (F : ∀ i, (P i).FullSubcategory ⥤ D)
    {k l : I} (e : k = l) {X : C} (hXk : P k X) (hXl : P l X)
    (Y : ∀ i, (P i).FullSubcategory) (f : ∀ i, X ⟶ (Y i).obj)
    (eX : (F k).obj ⟨X, hXk⟩ = (F l).obj ⟨X, hXl⟩) :
    (F k).map (ObjectProperty.homMk (f k) : ⟨X, hXk⟩ ⟶ Y k) ≫
        eqToHom (congrArg (fun i => (F i).obj (Y i)) e) =
      eqToHom eX ≫ (F l).map (ObjectProperty.homMk (f l) : ⟨X, hXl⟩ ⟶ Y l) := by
  cases e
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]

end RMod.Classification
