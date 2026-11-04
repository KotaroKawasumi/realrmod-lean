import Mathlib.CategoryTheory.Monoidal.Braided.Basic

set_option autoImplicit false
universe u v
namespace RMod.BrundanEllis.Stacking
open CategoryTheory CategoryTheory.MonoidalCategory
variable {M : Type u} [Category.{v} M] [MonoidalCategory M]

/-- Interchange with a specified middle arrow, allowing its two output
objects to have different auxiliary parity labels. -/
def interchangeMap (A B C D B' C' : M) (e : B ⊗ C ⟶ C' ⊗ B') :
    (A ⊗ B) ⊗ (C ⊗ D) ⟶ (A ⊗ C') ⊗ (B' ⊗ D) :=
  (α_ A B (C ⊗ D)).hom ≫ A ◁ (α_ B C D).inv ≫
    A ◁ (e ▷ D) ≫ A ◁ (α_ C' B' D).hom ≫ (α_ A C' (B' ⊗ D)).inv

/-- Expanding the two block crossings leaves a single ordinary interchange
of disjoint arrows. No global braiding or naturality of the middle arrows
is required. -/
theorem interchangeMap_associativity (A B B₁ B₂ C D D₁ E F : M)
    (bc : B ⊗ C ⟶ C ⊗ B₁) (de : D ⊗ E ⟶ E ⊗ D₁)
    (be : B₁ ⊗ E ⟶ E ⊗ B₂) :
    (interchangeMap A B C D B₁ C bc ▷ (E ⊗ F)) ≫
      interchangeMap (A ⊗ C) (B₁ ⊗ D) E F (B₂ ⊗ D₁) E
        ((α_ B₁ D E).hom ≫ B₁ ◁ de ≫ (α_ B₁ E D₁).inv ≫
          be ▷ D₁ ≫ (α_ E B₂ D₁).hom) ≫
      ((α_ A C E).hom ⊗ₘ (α_ B₂ D₁ F).hom) =
    (α_ (A ⊗ B) (C ⊗ D) (E ⊗ F)).hom ≫
      (A ⊗ B) ◁ interchangeMap C D E F D₁ E de ≫
      interchangeMap A B (C ⊗ E) (D₁ ⊗ F) B₂ (C ⊗ E)
        ((α_ B C E).inv ≫ bc ▷ E ≫ (α_ C B₁ E).hom ≫
          C ◁ be ≫ (α_ C E B₂).inv) := by
  unfold interchangeMap
  calc
    _ = 𝟙 _ ⊗≫
      A ◁ (bc ▷ (D ⊗ E) ≫ (C ⊗ B₁) ◁ de) ▷ F ⊗≫
        A ◁ C ◁ be ▷ D₁ ▷ F ⊗≫ 𝟙 _ := by monoidal
    _ = _ := by rw [← whisker_exchange]; monoidal

end RMod.BrundanEllis.Stacking
