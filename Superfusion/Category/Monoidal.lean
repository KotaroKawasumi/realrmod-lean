import Mathlib.CategoryTheory.Monoidal.Category
import Superfusion.Category.Supercategory

/-!
# Monoidal supercategories

The category of all morphisms in a supercategory does not satisfy Mathlib's
ordinary interchange axiom: interchanging odd morphisms introduces a Koszul
sign.  We therefore reuse only MonoidalCategoryStruct, which carries the
tensor, unit, associator, and unitor data, and state the signed axioms here.
-/

universe v u

open CategoryTheory MonoidalCategory

namespace Superfusion.Category

variable (K : Type*) [Field K]
variable (C : Type u) [Category.{v} C] [Preadditive C] [Linear K C]
  [MonoidalCategoryStruct C] [Supercategory K C]

/-- A monoidal supercategory: tensoring is bilinear and parity preserving,
composition of tensor products obeys super-interchange, and the structural
isomorphisms are even and satisfy the usual coherence identities. -/
class MonoidalSupercategory : Prop where
  /-- Tensoring homogeneous morphisms adds their parities. -/
  tensorHom_mem : ∀ {X₁ Y₁ X₂ Y₂ : C} {a b : ZMod 2}
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂),
    f ∈ homGrade K X₁ Y₁ a → g ∈ homGrade K X₂ Y₂ b →
    (f ⊗ₘ g) ∈ homGrade K (X₁ ⊗ X₂) (Y₁ ⊗ Y₂) (a + b)
  tensor_id : ∀ X Y : C, 𝟙 X ⊗ₘ 𝟙 Y = 𝟙 (X ⊗ Y)
  tensor_add_left : ∀ {X₁ Y₁ X₂ Y₂ : C} (f f' : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂),
    (f + f') ⊗ₘ g = f ⊗ₘ g + f' ⊗ₘ g
  tensor_add_right : ∀ {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g g' : X₂ ⟶ Y₂),
    f ⊗ₘ (g + g') = f ⊗ₘ g + f ⊗ₘ g'
  tensor_smul_left : ∀ {X₁ Y₁ X₂ Y₂ : C} (c : K)
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂),
    (c • f) ⊗ₘ g = c • (f ⊗ₘ g)
  tensor_smul_right : ∀ {X₁ Y₁ X₂ Y₂ : C} (c : K)
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂),
    f ⊗ₘ (c • g) = c • (f ⊗ₘ g)
  /-- Super-interchange, written in Mathlib's diagrammatic composition order. -/
  super_interchange : ∀ {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C} {b c : ZMod 2}
    (f : Y₁ ⟶ Z₁) (g : Y₂ ⟶ Z₂) (h : X₁ ⟶ Y₁) (k : X₂ ⟶ Y₂),
    g ∈ homGrade K Y₂ Z₂ b → h ∈ homGrade K X₁ Y₁ c →
    (h ⊗ₘ k) ≫ (f ⊗ₘ g) =
      koszulSign K b c • ((h ≫ f) ⊗ₘ (k ≫ g))
  whiskerLeft_eq : ∀ (X : C) {Y Z : C} (g : Y ⟶ Z),
    X ◁ g = 𝟙 X ⊗ₘ g
  whiskerRight_eq : ∀ {X Y : C} (f : X ⟶ Y) (Z : C),
    f ▷ Z = f ⊗ₘ 𝟙 Z
  associator_hom_mem : ∀ X Y Z : C,
    (α_ X Y Z).hom ∈ homGrade K ((X ⊗ Y) ⊗ Z) (X ⊗ (Y ⊗ Z)) 0
  associator_inv_mem : ∀ X Y Z : C,
    (α_ X Y Z).inv ∈ homGrade K (X ⊗ (Y ⊗ Z)) ((X ⊗ Y) ⊗ Z) 0
  associator_naturality : ∀ {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C}
    (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃),
    ((f₁ ⊗ₘ f₂) ⊗ₘ f₃) ≫ (α_ Y₁ Y₂ Y₃).hom =
      (α_ X₁ X₂ X₃).hom ≫ (f₁ ⊗ₘ (f₂ ⊗ₘ f₃))
  leftUnitor_hom_mem : ∀ X : C,
    (λ_ X).hom ∈ homGrade K (𝟙_ C ⊗ X) X 0
  leftUnitor_inv_mem : ∀ X : C,
    (λ_ X).inv ∈ homGrade K X (𝟙_ C ⊗ X) 0
  leftUnitor_naturality : ∀ {X Y : C} (f : X ⟶ Y),
    (𝟙_ C ◁ f) ≫ (λ_ Y).hom = (λ_ X).hom ≫ f
  rightUnitor_hom_mem : ∀ X : C,
    (ρ_ X).hom ∈ homGrade K (X ⊗ 𝟙_ C) X 0
  rightUnitor_inv_mem : ∀ X : C,
    (ρ_ X).inv ∈ homGrade K X (X ⊗ 𝟙_ C) 0
  rightUnitor_naturality : ∀ {X Y : C} (f : X ⟶ Y),
    (f ▷ 𝟙_ C) ≫ (ρ_ Y).hom = (ρ_ X).hom ≫ f
  pentagon : ∀ W X Y Z : C,
    (α_ W X Y).hom ▷ Z ≫ (α_ W (X ⊗ Y) Z).hom ≫ W ◁ (α_ X Y Z).hom =
      (α_ (W ⊗ X) Y Z).hom ≫ (α_ W X (Y ⊗ Z)).hom
  triangle : ∀ X Y : C,
    (α_ X (𝟙_ C) Y).hom ≫ X ◁ (λ_ Y).hom = (ρ_ X).hom ▷ Y

variable {C}

/-- Even coevaluation and evaluation morphisms exhibiting Y as a right dual
of X, with the two zigzag identities. -/
structure SuperExactPairing [MonoidalSupercategory K C] (X Y : C) where
  coeval : 𝟙_ C ⟶ X ⊗ Y
  eval : Y ⊗ X ⟶ 𝟙_ C
  coeval_mem : coeval ∈ homGrade K (𝟙_ C) (X ⊗ Y) 0
  eval_mem : eval ∈ homGrade K (Y ⊗ X) (𝟙_ C) 0
  coevaluation_evaluation :
    Y ◁ coeval ≫ (α_ Y X Y).inv ≫ eval ▷ Y =
      (ρ_ Y).hom ≫ (λ_ Y).inv
  evaluation_coevaluation :
    coeval ▷ X ≫ (α_ X Y X).hom ≫ X ◁ eval =
      (λ_ X).hom ≫ (ρ_ X).inv

/-- X has a right dual witnessed by an even exact pairing. -/
def HasSuperRightDual [MonoidalSupercategory K C] (X : C) : Prop :=
  ∃ Y : C, Nonempty (SuperExactPairing K X Y)

/-- X has a left dual witnessed by an even exact pairing. -/
def HasSuperLeftDual [MonoidalSupercategory K C] (X : C) : Prop :=
  ∃ Y : C, Nonempty (SuperExactPairing K Y X)

end Superfusion.Category
