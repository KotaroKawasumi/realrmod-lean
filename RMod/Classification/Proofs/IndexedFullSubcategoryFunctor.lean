import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.EqToHom

/-!
# Naturality of the equality comparison when a component index changes

An equality of indices identifies the same full-subcategory functor.
Membership proofs are propositions, so the induced object equality maps
commute with the images of every underlying morphism. This records the
actual equality maps used when g*(g^-1*k) is replaced by k.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

theorem indexedFullSubcategoryFunctor_eq_naturality
    {C D : Type*} [Category C] [Category D] {I : Type*}
    (P : I → ObjectProperty C) (F : ∀ i, (P i).FullSubcategory ⥤ D)
    {k l : I} (e : k = l) {X Y : C}
    (hXk : P k X) (hYk : P k Y) (hXl : P l X) (hYl : P l Y)
    (f : X ⟶ Y)
    (eX : (F k).obj ⟨X, hXk⟩ = (F l).obj ⟨X, hXl⟩)
    (eY : (F k).obj ⟨Y, hYk⟩ = (F l).obj ⟨Y, hYl⟩) :
    (F k).map (ObjectProperty.homMk f : ⟨X, hXk⟩ ⟶ ⟨Y, hYk⟩) ≫ eqToHom eY =
      eqToHom eX ≫ (F l).map (ObjectProperty.homMk f : ⟨X, hXl⟩ ⟶ ⟨Y, hYl⟩) := by
  cases e
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]

end RMod.Classification
