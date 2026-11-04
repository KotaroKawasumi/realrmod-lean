import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-! Unit constraints forced by the two local unit hexagons. Only the given
exchange isomorphisms and unit naturality are used; no global braiding is assumed. -/
set_option autoImplicit false
universe u v
namespace RMod.BrundanEllis.Stacking
open CategoryTheory CategoryTheory.MonoidalCategory
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- A unit hexagon and its unit naturality square force the standard right
unit exchange. No braiding on the whole category is required. -/
theorem exchange_rightUnit (X : C)
    (e : X ⊗ 𝟙_ C ≅ 𝟙_ C ⊗ X)
    (e₂ : X ⊗ (𝟙_ C ⊗ 𝟙_ C) ≅ (𝟙_ C ⊗ 𝟙_ C) ⊗ X)
    (hn : X ◁ (λ_ (𝟙_ C)).hom ≫ e.hom = e₂.hom ≫ (λ_ (𝟙_ C)).hom ▷ X)
    (hh : (α_ X (𝟙_ C) (𝟙_ C)).hom ≫ e₂.hom ≫ (α_ (𝟙_ C) (𝟙_ C) X).hom =
      e.hom ▷ 𝟙_ C ≫ (α_ (𝟙_ C) X (𝟙_ C)).hom ≫ (𝟙_ C) ◁ e.hom) :
    e.hom ≫ (λ_ X).hom = (ρ_ X).hom := by
  have ha : (α_ (𝟙_ C) (𝟙_ C) X).hom ≫
      (𝟙_ C ◁ e.inv) ≫ (α_ (𝟙_ C) X (𝟙_ C)).inv ≫ ((λ_ X).hom ▷ 𝟙_ C) =
      ((λ_ (𝟙_ C)).hom ▷ X) ≫ e.inv := by monoidal
  apply (whiskerRight_iff _ _).mp
  rw [comp_whiskerRight]
  calc
    (e.hom ▷ 𝟙_ C) ≫ ((λ_ X).hom ▷ 𝟙_ C) =
        (e.hom ▷ 𝟙_ C) ≫ (α_ (𝟙_ C) X (𝟙_ C)).hom ≫
          (𝟙_ C ◁ e.hom) ≫ (𝟙_ C ◁ e.inv) ≫
            (α_ (𝟙_ C) X (𝟙_ C)).inv ≫ ((λ_ X).hom ▷ 𝟙_ C) := by simp
    _ = (α_ X (𝟙_ C) (𝟙_ C)).hom ≫ e₂.hom ≫ (α_ (𝟙_ C) (𝟙_ C) X).hom ≫
        (𝟙_ C ◁ e.inv) ≫ (α_ (𝟙_ C) X (𝟙_ C)).inv ≫ ((λ_ X).hom ▷ 𝟙_ C) := by
      rw [← reassoc_of% hh]
    _ = (α_ X (𝟙_ C) (𝟙_ C)).hom ≫ e₂.hom ≫ ((λ_ (𝟙_ C)).hom ▷ X) ≫ e.inv := by rw [ha]
    _ = (α_ X (𝟙_ C) (𝟙_ C)).hom ≫ (X ◁ (λ_ (𝟙_ C)).hom) ≫ e.hom ≫ e.inv := by
      rw [← reassoc_of% hn]
    _ = (ρ_ X).hom ▷ 𝟙_ C := by simp

/-- The reverse unit hexagon similarly fixes the left unit exchange. -/
theorem exchange_leftUnit (X : C)
    (e : 𝟙_ C ⊗ X ≅ X ⊗ 𝟙_ C)
    (e₂ : (𝟙_ C ⊗ 𝟙_ C) ⊗ X ≅ X ⊗ (𝟙_ C ⊗ 𝟙_ C))
    (hn : (ρ_ (𝟙_ C)).hom ▷ X ≫ e.hom = e₂.hom ≫ X ◁ (ρ_ (𝟙_ C)).hom)
    (hh : (α_ (𝟙_ C) (𝟙_ C) X).inv ≫ e₂.hom ≫ (α_ X (𝟙_ C) (𝟙_ C)).inv =
      (𝟙_ C) ◁ e.hom ≫ (α_ (𝟙_ C) X (𝟙_ C)).inv ≫ e.hom ▷ 𝟙_ C) :
    e.hom ≫ (ρ_ X).hom = (λ_ X).hom := by
  have ha : (α_ X (𝟙_ C) (𝟙_ C)).inv ≫
      (e.inv ▷ 𝟙_ C) ≫ (α_ (𝟙_ C) X (𝟙_ C)).hom ≫ (𝟙_ C ◁ (ρ_ X).hom) =
      (X ◁ (ρ_ (𝟙_ C)).hom) ≫ e.inv := by monoidal
  apply (whiskerLeft_iff _ _).mp
  rw [whiskerLeft_comp]
  calc
    (𝟙_ C ◁ e.hom) ≫ (𝟙_ C ◁ (ρ_ X).hom) =
        (𝟙_ C ◁ e.hom) ≫ (α_ (𝟙_ C) X (𝟙_ C)).inv ≫
          (e.hom ▷ 𝟙_ C) ≫ (e.inv ▷ 𝟙_ C) ≫
            (α_ (𝟙_ C) X (𝟙_ C)).hom ≫ (𝟙_ C ◁ (ρ_ X).hom) := by simp
    _ = (α_ (𝟙_ C) (𝟙_ C) X).inv ≫ e₂.hom ≫ (α_ X (𝟙_ C) (𝟙_ C)).inv ≫
        (e.inv ▷ 𝟙_ C) ≫ (α_ (𝟙_ C) X (𝟙_ C)).hom ≫ (𝟙_ C ◁ (ρ_ X).hom) := by
      rw [← reassoc_of% hh]
    _ = (α_ (𝟙_ C) (𝟙_ C) X).inv ≫ e₂.hom ≫ (X ◁ (ρ_ (𝟙_ C)).hom) ≫ e.inv := by rw [ha]
    _ = (α_ (𝟙_ C) (𝟙_ C) X).inv ≫ ((ρ_ (𝟙_ C)).hom ▷ X) ≫ e.hom ≫ e.inv := by
      rw [← reassoc_of% hn]
    _ = 𝟙_ C ◁ (λ_ X).hom := by simp

end RMod.BrundanEllis.Stacking
