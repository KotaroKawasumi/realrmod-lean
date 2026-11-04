import Mathlib.CategoryTheory.Monoidal.Transport

/-!
# Monoidal comparisons before coherence has been established

Mathlib's monoidal functor interface assumes coherence on both sides.
During reconstruction the target pentagon is still a conclusion. These
proof-side structures retain its tensor and unit comparison first, with
the functor diagrams in a dependent Prop. The isomorphisms use Mathlib's
existing interface; no new category, group, or isomorphism is introduced.
-/

set_option autoImplicit false
universe u₁ v₁ u₂ v₂

namespace RMod.Classification

open CategoryTheory CategoryTheory.MonoidalCategory

/-- The tensor is a bifunctor and its structure maps are natural.
Pentagon and triangle are deliberately absent from this adjective. -/
structure TensorStructuralLaws (D : Type u₂) [Category.{v₂} D]
    [MonoidalCategoryStruct D] : Prop where
  tensor_id : ∀ X Y : D, (𝟙 X) ⊗ₘ (𝟙 Y) = 𝟙 (X ⊗ Y)
  tensor_comp : ∀ {X₁ X₂ X₃ Y₁ Y₂ Y₃ : D}
    (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃) (h : Y₁ ⟶ Y₂) (k : Y₂ ⟶ Y₃),
    (f ≫ g) ⊗ₘ (h ≫ k) = (f ⊗ₘ h) ≫ (g ⊗ₘ k)
  whisker_left : ∀ (X : D) {Y Z : D} (f : Y ⟶ Z), X ◁ f = (𝟙 X) ⊗ₘ f
  whisker_right : ∀ {X Y : D} (f : X ⟶ Y) (Z : D), f ▷ Z = f ⊗ₘ (𝟙 Z)
  associator_naturality : ∀ {X₁ X₂ X₃ Y₁ Y₂ Y₃ : D}
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) (h : X₃ ⟶ Y₃),
    ((f ⊗ₘ g) ⊗ₘ h) ≫ (α_ Y₁ Y₂ Y₃).hom =
      (α_ X₁ X₂ X₃).hom ≫ (f ⊗ₘ (g ⊗ₘ h))
  left_unitor_naturality : ∀ {X Y : D} (f : X ⟶ Y),
    ((𝟙 (𝟙_ D)) ⊗ₘ f) ≫ (λ_ Y).hom = (λ_ X).hom ≫ f
  right_unitor_naturality : ∀ {X Y : D} (f : X ⟶ Y),
    (f ⊗ₘ (𝟙 (𝟙_ D))) ≫ (ρ_ Y).hom = (ρ_ X).hom ≫ f

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategoryStruct C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategoryStruct D]

structure MonoidalComparisonData (F : C ⥤ D) where
  tensor : ∀ X Y : C, F.obj X ⊗ F.obj Y ≅ F.obj (X ⊗ Y)
  unit : 𝟙_ D ≅ F.obj (𝟙_ C)

structure MonoidalComparisonLaws (F : C ⥤ D) (d : MonoidalComparisonData F) : Prop where
  naturality : ∀ {X X' Y Y' : C} (f : X ⟶ X') (g : Y ⟶ Y'),
    (F.map f ⊗ₘ F.map g) ≫ (d.tensor X' Y').hom =
      (d.tensor X Y).hom ≫ F.map (f ⊗ₘ g)
  associativity : ∀ X Y Z : C,
    ((d.tensor X Y).hom ⊗ₘ (𝟙 (F.obj Z))) ≫
      (d.tensor (X ⊗ Y) Z).hom ≫ F.map (α_ X Y Z).hom =
    (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom ≫
      ((𝟙 (F.obj X)) ⊗ₘ (d.tensor Y Z).hom) ≫ (d.tensor X (Y ⊗ Z)).hom
  left_unit : ∀ X : C,
    (d.unit.hom ⊗ₘ (𝟙 (F.obj X))) ≫ (d.tensor (𝟙_ C) X).hom ≫
      F.map (λ_ X).hom = (λ_ (F.obj X)).hom
  right_unit : ∀ X : C,
    ((𝟙 (F.obj X)) ⊗ₘ d.unit.hom) ≫ (d.tensor X (𝟙_ C)).hom ≫
      F.map (ρ_ X).hom = (ρ_ (F.obj X)).hom

structure MonoidalComparison (F : C ⥤ D) where
  data : MonoidalComparisonData F
  laws : MonoidalComparisonLaws F data

end RMod.Classification
