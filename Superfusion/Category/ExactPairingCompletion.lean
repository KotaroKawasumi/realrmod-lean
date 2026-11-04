import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic
import Mathlib.CategoryTheory.Bicategory.SingleObj
import Superfusion.Category.Even

/-!
# Completing exact pairings from one snake identity

This file records a basis-free completion principle for exact pairings.
When one normalized snake is the identity, the other is idempotent and is
absorbed by the coevaluation.  A nonzero-object hypothesis and the even
Schur property therefore make the second snake invertible, hence equal to
the identity.
-/

set_option autoImplicit false

universe u v

open CategoryTheory MonoidalCategory

namespace Superfusion.Category

noncomputable section

variable {D : Type u} [Category.{v} D]
variable {X Y : D}

section Definitions

variable [MonoidalCategoryStruct D]

/-- The normalized snake endomorphism of `X`. -/
def normalizedXSnake
    (η : 𝟙_ D ⟶ X ⊗ Y) (ε : Y ⊗ X ⟶ 𝟙_ D) : X ⟶ X :=
  (λ_ X).inv ≫
    η ▷ X ≫
      (α_ X Y X).hom ≫
        X ◁ ε ≫
          (ρ_ X).hom

/-- The normalized snake endomorphism of `Y`. -/
def normalizedYSnake
    (η : 𝟙_ D ⟶ X ⊗ Y) (ε : Y ⊗ X ⟶ 𝟙_ D) : Y ⟶ Y :=
  (ρ_ Y).inv ≫
    Y ◁ η ≫
      (α_ Y X Y).inv ≫
        ε ▷ Y ≫
          (λ_ Y).hom

end Definitions

section Ordinary

variable [MonoidalCategory D]

lemma normalizedXSnake_eq_id_iff
    (η : 𝟙_ D ⟶ X ⊗ Y) (ε : Y ⊗ X ⟶ 𝟙_ D) :
    normalizedXSnake η ε = 𝟙 X ↔
      η ▷ X ≫ (α_ X Y X).hom ≫ X ◁ ε =
        (λ_ X).hom ≫ (ρ_ X).inv := by
  constructor
  · intro h
    rw [← cancel_epi (λ_ X).inv, ← cancel_mono (ρ_ X).hom]
    simpa [normalizedXSnake, Category.assoc] using h
  · intro h
    calc
      normalizedXSnake η ε =
          (λ_ X).inv ≫
            (η ▷ X ≫ (α_ X Y X).hom ≫ X ◁ ε) ≫
              (ρ_ X).hom := by simp [normalizedXSnake]
      _ = (λ_ X).inv ≫
            ((λ_ X).hom ≫ (ρ_ X).inv) ≫
              (ρ_ X).hom := by rw [h]
      _ = 𝟙 X := by simp

lemma normalizedYSnake_eq_id_iff
    (η : 𝟙_ D ⟶ X ⊗ Y) (ε : Y ⊗ X ⟶ 𝟙_ D) :
    normalizedYSnake η ε = 𝟙 Y ↔
      Y ◁ η ≫ (α_ Y X Y).inv ≫ ε ▷ Y =
        (ρ_ Y).hom ≫ (λ_ Y).inv := by
  constructor
  · intro h
    rw [← cancel_epi (ρ_ Y).inv, ← cancel_mono (λ_ Y).hom]
    simpa [normalizedYSnake, Category.assoc] using h
  · intro h
    calc
      normalizedYSnake η ε =
          (ρ_ Y).inv ≫
            (Y ◁ η ≫ (α_ Y X Y).inv ≫ ε ▷ Y) ≫
              (λ_ Y).hom := by simp [normalizedYSnake]
      _ = (ρ_ Y).inv ≫
            ((ρ_ Y).hom ≫ (λ_ Y).inv) ≫
              (λ_ Y).hom := by rw [h]
      _ = 𝟙 Y := by simp

private abbrev leftZigzagM
    (η : 𝟙_ D ⟶ X ⊗ Y) (ε : Y ⊗ X ⟶ 𝟙_ D) :=
  η ▷ X ⊗≫ X ◁ ε

private abbrev rightZigzagM
    (η : 𝟙_ D ⟶ X ⊗ Y) (ε : Y ⊗ X ⟶ 𝟙_ D) :=
  Y ◁ η ⊗≫ ε ▷ Y

private lemma rightZigzagM_idempotent_of_left_triangle
    (η : 𝟙_ D ⟶ X ⊗ Y) (ε : Y ⊗ X ⟶ 𝟙_ D)
    (h : leftZigzagM η ε =
      (λ_ X).hom ≫ (ρ_ X).inv) :
    rightZigzagM η ε ⊗≫ rightZigzagM η ε =
      rightZigzagM η ε := by
  exact Bicategory.rightZigzag_idempotent_of_left_triangle
    (B := MonoidalSingleObj D)
    (a := MonoidalSingleObj.star D)
    (b := MonoidalSingleObj.star D)
    (f := X) (g := Y) η ε h

lemma normalizedYSnake_idempotent
    (η : 𝟙_ D ⟶ X ⊗ Y) (ε : Y ⊗ X ⟶ 𝟙_ D)
    (h : normalizedXSnake η ε = 𝟙 X) :
    normalizedYSnake η ε ≫ normalizedYSnake η ε =
      normalizedYSnake η ε := by
  have hraw := (normalizedXSnake_eq_id_iff η ε).mp h
  have hzig :
      leftZigzagM η ε = (λ_ X).hom ≫ (ρ_ X).inv := by
    calc
      leftZigzagM η ε =
          η ▷ X ≫ (α_ X Y X).hom ≫ X ◁ ε := by
            monoidal
      _ = _ := hraw
  have hz := rightZigzagM_idempotent_of_left_triangle η ε hzig
  dsimp only [normalizedYSnake]
  rw [← cancel_epi (ρ_ Y).hom, ← cancel_mono (λ_ Y).inv]
  simp only [Category.assoc, Iso.hom_inv_id_assoc,
    Iso.hom_inv_id, Category.comp_id]
  calc
    _ = rightZigzagM η ε ⊗≫ rightZigzagM η ε := by
      monoidal
    _ = rightZigzagM η ε := hz
    _ = _ := by monoidal

lemma coevaluation_absorbs_normalizedYSnake
    (η : 𝟙_ D ⟶ X ⊗ Y) (ε : Y ⊗ X ⟶ 𝟙_ D)
    (h : normalizedXSnake η ε = 𝟙 X) :
    η ≫ X ◁ normalizedYSnake η ε = η := by
  have hraw := (normalizedXSnake_eq_id_iff η ε).mp h
  have hzig :
      leftZigzagM η ε = (λ_ X).hom ≫ (ρ_ X).inv := by
    calc
      leftZigzagM η ε =
          η ▷ X ≫ (α_ X Y X).hom ≫ X ◁ ε := by
            monoidal
      _ = _ := hraw
  calc
    η ≫ X ◁ normalizedYSnake η ε =
        𝟙 (𝟙_ D) ⊗≫
          (η ▷ 𝟙_ D ≫ (X ⊗ Y) ◁ η) ⊗≫
            (X ◁ ε) ▷ Y ⊗≫ 𝟙 _ := by
          dsimp only [normalizedYSnake]
          monoidal
    _ = 𝟙 (𝟙_ D) ⊗≫
          (𝟙_ D ◁ η ≫ η ▷ (X ⊗ Y)) ⊗≫
            (X ◁ ε) ▷ Y ⊗≫ 𝟙 _ := by
          rw [whisker_exchange]
    _ = η ⊗≫ (leftZigzagM η ε) ▷ Y ⊗≫ 𝟙 _ := by
          monoidal
    _ = η ⊗≫
        ((λ_ X).hom ≫ (ρ_ X).inv) ▷ Y ⊗≫ 𝟙 _ := by rw [hzig]
    _ = η := by monoidal

/-- Complete an ordinary exact pairing from one normalized snake identity
when the opposite normalized snake is invertible. -/
@[implicit_reducible]
def exactPairingOfNormalizedXSnakeOfIsIso
    (η : 𝟙_ D ⟶ X ⊗ Y) (ε : Y ⊗ X ⟶ 𝟙_ D)
    (h : normalizedXSnake η ε = 𝟙 X)
    [IsIso (normalizedYSnake η ε)] :
    ExactPairing X Y where
  coevaluation' := η
  evaluation' := ε
  evaluation_coevaluation' :=
    (normalizedXSnake_eq_id_iff η ε).mp h
  coevaluation_evaluation' := by
    apply (normalizedYSnake_eq_id_iff η ε).mp
    apply (cancel_epi (normalizedYSnake η ε)).mp
    simpa using normalizedYSnake_idempotent η ε h

end Ordinary

section Super

variable {K : Type*} [Field K]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear K C]
  [Supercategory K C] [MonoidalCategoryStruct C]
  [MonoidalSupercategory K C]
variable {X Y : C}

/-- The normalized `X`-snake has the sum of the degrees of its
coevaluation and evaluation. -/
theorem normalizedXSnake_mem
    {a b : ZMod 2}
    (η : 𝟙_ C ⟶ X ⊗ Y) (ε : Y ⊗ X ⟶ 𝟙_ C)
    (hη : η ∈ homGrade K (𝟙_ C) (X ⊗ Y) a)
    (hε : ε ∈ homGrade K (Y ⊗ X) (𝟙_ C) b) :
    normalizedXSnake η ε ∈ homGrade K X X (a + b) := by
  have hηX :
      η ▷ X ∈
        homGrade K (𝟙_ C ⊗ X) ((X ⊗ Y) ⊗ X) a := by
    rw [MonoidalSupercategory.whiskerRight_eq (K := K)]
    simpa only [add_zero] using
      MonoidalSupercategory.tensorHom_mem (K := K)
        η (𝟙 X) hη (Supercategory.id_mem_even X)
  have hXε :
      X ◁ ε ∈
        homGrade K (X ⊗ (Y ⊗ X)) (X ⊗ 𝟙_ C) b := by
    rw [MonoidalSupercategory.whiskerLeft_eq (K := K)]
    simpa only [zero_add] using
      MonoidalSupercategory.tensorHom_mem (K := K)
        (𝟙 X) ε (Supercategory.id_mem_even X) hε
  have h₁ :=
    Supercategory.comp_mem (λ_ X).inv (η ▷ X)
      (MonoidalSupercategory.leftUnitor_inv_mem (K := K) X) hηX
  have h₂ :=
    Supercategory.comp_mem ((λ_ X).inv ≫ η ▷ X)
      (α_ X Y X).hom h₁
      (MonoidalSupercategory.associator_hom_mem (K := K) X Y X)
  have h₃ :=
    Supercategory.comp_mem
      (((λ_ X).inv ≫ η ▷ X) ≫ (α_ X Y X).hom)
      (X ◁ ε) h₂ hXε
  have h₄ :=
    Supercategory.comp_mem
      ((((λ_ X).inv ≫ η ▷ X) ≫ (α_ X Y X).hom) ≫ X ◁ ε)
      (ρ_ X).hom h₃
      (MonoidalSupercategory.rightUnitor_hom_mem (K := K) X)
  simpa only [normalizedXSnake, homGrade, Category.assoc, zero_add,
    add_zero, add_assoc] using h₄

/-- Moving a homogeneous endomorphism of `X` from the left of the
normalized `X`-snake into the evaluation introduces no sign when the
coevaluation is even. -/
theorem normalizedXSnake_evaluation_action
    {a b : ZMod 2}
    (η : 𝟙_ C ⟶ X ⊗ Y) (ε : Y ⊗ X ⟶ 𝟙_ C) (f : X ⟶ X)
    (hη : η ∈ homGrade K (𝟙_ C) (X ⊗ Y) 0)
    (hε : ε ∈ homGrade K (Y ⊗ X) (𝟙_ C) b)
    (hf : f ∈ homGrade K X X a) :
    normalizedXSnake η ((Y ◁ f) ≫ ε) =
      f ≫ normalizedXSnake η ε := by
  have hUnitor :
      f ≫ (λ_ X).inv =
        (λ_ X).inv ≫ (𝟙_ C ◁ f) := by
    apply (cancel_epi (λ_ X).hom).mp
    simp only [Iso.hom_inv_id_assoc]
    rw [← Category.assoc,
      ← MonoidalSupercategory.leftUnitor_naturality (K := K) f]
    simp
  have hUnitTensor :
      (𝟙_ C ◁ f) ≫ (η ▷ X) = η ⊗ₘ f := by
    have h :=
      MonoidalSupercategory.super_interchange
        (K := K) η (𝟙 X) (𝟙 (𝟙_ C)) f
        (Supercategory.id_mem_even X)
        (Supercategory.id_mem_even (𝟙_ C))
    rw [MonoidalSupercategory.whiskerLeft_eq (K := K),
      MonoidalSupercategory.whiskerRight_eq (K := K)]
    simpa only [Category.id_comp, Category.comp_id, koszulSign,
      mul_zero, ZMod.val_zero, pow_zero, one_smul] using h
  have hTensorFactor :
      η ⊗ₘ f =
        (η ▷ X) ≫ (𝟙 (X ⊗ Y) ⊗ₘ f) := by
    have h :=
      MonoidalSupercategory.super_interchange
        (K := K) (𝟙 (X ⊗ Y)) f η (𝟙 X) hf hη
    rw [MonoidalSupercategory.whiskerRight_eq (K := K)]
    simpa only [Category.id_comp, Category.comp_id, koszulSign,
      mul_zero, ZMod.val_zero, pow_zero, one_smul] using h.symm
  have hAssociator :
      (𝟙 (X ⊗ Y) ⊗ₘ f) ≫ (α_ X Y X).hom =
        (α_ X Y X).hom ≫
          (𝟙 X ⊗ₘ (𝟙 Y ⊗ₘ f)) := by
    simpa only [MonoidalSupercategory.tensor_id (K := K)] using
      (MonoidalSupercategory.associator_naturality
        (K := K) (𝟙 X) (𝟙 Y) f)
  have hWhisker :
      (𝟙 X ⊗ₘ (𝟙 Y ⊗ₘ f)) ≫ (X ◁ ε) =
        X ◁ ((Y ◁ f) ≫ ε) := by
    have h :=
      MonoidalSupercategory.super_interchange
        (K := K) (𝟙 X) ε (𝟙 X) (𝟙 Y ⊗ₘ f)
        hε (Supercategory.id_mem_even X)
    rw [MonoidalSupercategory.whiskerLeft_eq (K := K),
      MonoidalSupercategory.whiskerLeft_eq (K := K),
      MonoidalSupercategory.whiskerLeft_eq (K := K)]
    simpa only [Category.id_comp, koszulSign, mul_zero,
      ZMod.val_zero, pow_zero, one_smul] using h
  symm
  calc
    f ≫ normalizedXSnake η ε =
        (f ≫ (λ_ X).inv) ≫
          (η ▷ X) ≫ (α_ X Y X).hom ≫
            (X ◁ ε) ≫ (ρ_ X).hom := by
      simp only [normalizedXSnake, Category.assoc]
    _ = ((λ_ X).inv ≫ (𝟙_ C ◁ f)) ≫
          (η ▷ X) ≫ (α_ X Y X).hom ≫
            (X ◁ ε) ≫ (ρ_ X).hom := by rw [hUnitor]
    _ = (λ_ X).inv ≫
          ((𝟙_ C ◁ f) ≫ (η ▷ X)) ≫
            (α_ X Y X).hom ≫
              (X ◁ ε) ≫ (ρ_ X).hom := by
      simp only [Category.assoc]
    _ = (λ_ X).inv ≫
          (η ⊗ₘ f) ≫ (α_ X Y X).hom ≫
            (X ◁ ε) ≫ (ρ_ X).hom := by rw [hUnitTensor]
    _ = (λ_ X).inv ≫
          ((η ▷ X) ≫ (𝟙 (X ⊗ Y) ⊗ₘ f)) ≫
            (α_ X Y X).hom ≫
              (X ◁ ε) ≫ (ρ_ X).hom := by rw [hTensorFactor]
    _ = (λ_ X).inv ≫
          (η ▷ X) ≫
            ((𝟙 (X ⊗ Y) ⊗ₘ f) ≫ (α_ X Y X).hom) ≫
              (X ◁ ε) ≫ (ρ_ X).hom := by
      simp only [Category.assoc]
    _ = (λ_ X).inv ≫
          (η ▷ X) ≫
            ((α_ X Y X).hom ≫
              (𝟙 X ⊗ₘ (𝟙 Y ⊗ₘ f))) ≫
                (X ◁ ε) ≫ (ρ_ X).hom := by rw [hAssociator]
    _ = (λ_ X).inv ≫
          (η ▷ X) ≫ (α_ X Y X).hom ≫
            ((𝟙 X ⊗ₘ (𝟙 Y ⊗ₘ f)) ≫
              (X ◁ ε)) ≫ (ρ_ X).hom := by
      simp only [Category.assoc]
    _ = (λ_ X).inv ≫
          (η ▷ X) ≫ (α_ X Y X).hom ≫
            (X ◁ ((Y ◁ f) ≫ ε)) ≫ (ρ_ X).hom := by rw [hWhisker]
    _ = normalizedXSnake η ((Y ◁ f) ≫ ε) := by
      rfl

/-- Absorb the inverse normalized `X`-snake into the evaluation. -/
def normalizeEvaluationByXSnake
    (η : 𝟙_ C ⟶ X ⊗ Y) (ε : Y ⊗ X ⟶ 𝟙_ C)
    [IsIso (normalizedXSnake η ε)] :
    Y ⊗ X ⟶ 𝟙_ C :=
  (Y ◁ inv (normalizedXSnake η ε)) ≫ ε

/-- Normalizing the evaluation makes it even when its original degree is
the degree of the invertible normalized `X`-snake. -/
theorem normalizeEvaluationByXSnake_mem_even
    {e : ZMod 2}
    (η : 𝟙_ C ⟶ X ⊗ Y) (ε : Y ⊗ X ⟶ 𝟙_ C)
    (hη : η ∈ homGrade K (𝟙_ C) (X ⊗ Y) 0)
    (hε : ε ∈ homGrade K (Y ⊗ X) (𝟙_ C) e)
    [IsIso (normalizedXSnake η ε)] :
    normalizeEvaluationByXSnake η ε ∈
      homGrade K (Y ⊗ X) (𝟙_ C) 0 := by
  have hSnake :
      normalizedXSnake η ε ∈ homGrade K X X e := by
    simpa only [zero_add] using
      normalizedXSnake_mem η ε hη hε
  have hInv :
      inv (normalizedXSnake η ε) ∈ homGrade K X X e := by
    simpa only [asIso_inv] using
      inv_mem_homGrade_of_hom_mem
        (K := K) (asIso (normalizedXSnake η ε)) e hSnake
  have hWhisker :
      Y ◁ inv (normalizedXSnake η ε) ∈
        homGrade K (Y ⊗ X) (Y ⊗ X) e := by
    rw [MonoidalSupercategory.whiskerLeft_eq (K := K)]
    simpa only [zero_add] using
      MonoidalSupercategory.tensorHom_mem
        (K := K) (𝟙 Y) (inv (normalizedXSnake η ε))
        (Supercategory.id_mem_even Y) hInv
  simpa only [normalizeEvaluationByXSnake, homGrade,
    ZModModule.add_self] using
    Supercategory.comp_mem
      (Y ◁ inv (normalizedXSnake η ε)) ε hWhisker hε

/-- Evaluation normalization makes the normalized `X`-snake the identity. -/
theorem normalizedXSnake_normalizeEvaluationByXSnake
    {e : ZMod 2}
    (η : 𝟙_ C ⟶ X ⊗ Y) (ε : Y ⊗ X ⟶ 𝟙_ C)
    (hη : η ∈ homGrade K (𝟙_ C) (X ⊗ Y) 0)
    (hε : ε ∈ homGrade K (Y ⊗ X) (𝟙_ C) e)
    [IsIso (normalizedXSnake η ε)] :
    normalizedXSnake η (normalizeEvaluationByXSnake η ε) =
      𝟙 X := by
  have hSnake :
      normalizedXSnake η ε ∈ homGrade K X X e := by
    simpa only [zero_add] using
      normalizedXSnake_mem η ε hη hε
  have hInv :
      inv (normalizedXSnake η ε) ∈ homGrade K X X e := by
    simpa only [asIso_inv] using
      inv_mem_homGrade_of_hom_mem
        (K := K) (asIso (normalizedXSnake η ε)) e hSnake
  rw [normalizeEvaluationByXSnake,
    normalizedXSnake_evaluation_action η ε
      (inv (normalizedXSnake η ε)) hη hε hInv]
  simpa only [Category.comp_id] using
    IsIso.inv_hom_id_assoc (normalizedXSnake η ε) (𝟙 X)

/-- Simultaneously transport the two objects in a normalized `X`-snake
across homogeneous isomorphisms of the same degree.

The raw transport acquires exactly one Koszul sign: the target-side map on
`X` crosses the source-side map on `Y`. -/
theorem normalizedXSnake_simultaneous_homogeneous_transport
    {X' Y' : C} {d : ZMod 2}
    (η : 𝟙_ C ⟶ X' ⊗ Y') (ε : Y' ⊗ X' ⟶ 𝟙_ C)
    (i : HomogeneousIso K d X X')
    (j : HomogeneousIso K d Y Y')
    (hη : η ∈ homGrade K (𝟙_ C) (X' ⊗ Y') 0)
    (hε : ε ∈ homGrade K (Y' ⊗ X') (𝟙_ C) 0) :
    normalizedXSnake
        (η ≫ (i.iso.inv ⊗ₘ j.iso.inv))
        ((j.iso.hom ⊗ₘ i.iso.hom) ≫ ε) =
      koszulSign K d d •
        (i.iso.hom ≫ normalizedXSnake η ε ≫ i.iso.inv) := by
  let T : X' ⊗ Y' ⟶ X ⊗ Y :=
    i.iso.inv ⊗ₘ j.iso.inv
  let J : Y ⊗ X ⟶ Y' ⊗ X' :=
    j.iso.hom ⊗ₘ i.iso.hom
  have hT :
      T ∈ homGrade K (X' ⊗ Y') (X ⊗ Y) 0 := by
    simpa only [T, ZModModule.add_self] using
      MonoidalSupercategory.tensorHom_mem
        (K := K) i.iso.inv j.iso.inv i.inv_mem j.inv_mem
  have hJ :
      J ∈ homGrade K (Y ⊗ X) (Y' ⊗ X') 0 := by
    simpa only [J, ZModModule.add_self] using
      MonoidalSupercategory.tensorHom_mem
        (K := K) j.iso.hom i.iso.hom j.hom_mem i.hom_mem
  have hCoevalWhisker :
      (η ≫ T) ▷ X = (η ▷ X) ≫ (T ▷ X) := by
    have h :=
      MonoidalSupercategory.super_interchange
        (K := K) T (𝟙 X) η (𝟙 X)
        (Supercategory.id_mem_even X) hη
    rw [MonoidalSupercategory.whiskerRight_eq (K := K),
      MonoidalSupercategory.whiskerRight_eq (K := K),
      MonoidalSupercategory.whiskerRight_eq (K := K)]
    simpa only [koszulSign, mul_zero, ZMod.val_zero, pow_zero,
      one_smul, Category.comp_id] using h.symm
  have hEvalWhisker :
      X ◁ (J ≫ ε) = (X ◁ J) ≫ (X ◁ ε) := by
    have h :=
      MonoidalSupercategory.super_interchange
        (K := K) (𝟙 X) ε (𝟙 X) J hε
        (Supercategory.id_mem_even X)
    rw [MonoidalSupercategory.whiskerLeft_eq (K := K) X (J ≫ ε),
      MonoidalSupercategory.whiskerLeft_eq (K := K) X J,
      MonoidalSupercategory.whiskerLeft_eq (K := K) X ε]
    simpa only [koszulSign, mul_zero, ZMod.val_zero, pow_zero,
      one_smul, Category.id_comp] using h.symm
  have hTAssociator :
      (T ▷ X) ≫ (α_ X Y X).hom =
        (α_ X' Y' X).hom ≫
          (i.iso.inv ⊗ₘ (j.iso.inv ⊗ₘ 𝟙 X)) := by
    rw [MonoidalSupercategory.whiskerRight_eq (K := K)]
    exact MonoidalSupercategory.associator_naturality
      (K := K) i.iso.inv j.iso.inv (𝟙 X)
  have hCore :
      (i.iso.inv ⊗ₘ (j.iso.inv ⊗ₘ 𝟙 X)) ≫
          (𝟙 X ⊗ₘ J) =
        koszulSign K d d •
          (i.iso.inv ⊗ₘ (𝟙 Y' ⊗ₘ i.iso.hom)) := by
    have hOuter :=
      MonoidalSupercategory.super_interchange
        (K := K) (𝟙 X) J i.iso.inv
          (j.iso.inv ⊗ₘ 𝟙 X) hJ i.inv_mem
    have hOuter' :
        (i.iso.inv ⊗ₘ (j.iso.inv ⊗ₘ 𝟙 X)) ≫
            (𝟙 X ⊗ₘ J) =
          i.iso.inv ⊗ₘ
            ((j.iso.inv ⊗ₘ 𝟙 X) ≫ J) := by
      simpa only [koszulSign, zero_mul, ZMod.val_zero, pow_zero,
        one_smul, Category.comp_id] using hOuter
    have hInner :=
      MonoidalSupercategory.super_interchange
        (K := K) j.iso.hom i.iso.hom j.iso.inv (𝟙 X)
        i.hom_mem j.inv_mem
    have hInner' :
        (j.iso.inv ⊗ₘ 𝟙 X) ≫ J =
          koszulSign K d d •
            (𝟙 Y' ⊗ₘ i.iso.hom) := by
      simpa only [J, Iso.inv_hom_id, Category.id_comp,
        Category.comp_id] using hInner
    calc
      (i.iso.inv ⊗ₘ (j.iso.inv ⊗ₘ 𝟙 X)) ≫
            (𝟙 X ⊗ₘ J) =
          i.iso.inv ⊗ₘ
            ((j.iso.inv ⊗ₘ 𝟙 X) ≫ J) := hOuter'
      _ = i.iso.inv ⊗ₘ
            (koszulSign K d d •
              (𝟙 Y' ⊗ₘ i.iso.hom)) := by rw [hInner']
      _ = koszulSign K d d •
            (i.iso.inv ⊗ₘ (𝟙 Y' ⊗ₘ i.iso.hom)) := by
          rw [MonoidalSupercategory.tensor_smul_right (K := K)]
  have hQFactor :
      (𝟙 X' ⊗ₘ (𝟙 Y' ⊗ₘ i.iso.hom)) ≫
          (i.iso.inv ⊗ₘ 𝟙 (Y' ⊗ X')) =
        i.iso.inv ⊗ₘ (𝟙 Y' ⊗ₘ i.iso.hom) := by
    have h :=
      MonoidalSupercategory.super_interchange
        (K := K) i.iso.inv (𝟙 (Y' ⊗ X')) (𝟙 X')
          (𝟙 Y' ⊗ₘ i.iso.hom)
        (Supercategory.id_mem_even (Y' ⊗ X'))
        (Supercategory.id_mem_even X')
    simpa only [koszulSign, mul_zero, ZMod.val_zero, pow_zero,
      one_smul, Category.id_comp, Category.comp_id] using h
  have hInputTensor :
      ((𝟙 X' ⊗ₘ 𝟙 Y') ⊗ₘ i.iso.hom) ≫
          (α_ X' Y' X').hom =
        (α_ X' Y' X).hom ≫
          (𝟙 X' ⊗ₘ (𝟙 Y' ⊗ₘ i.iso.hom)) := by
    exact MonoidalSupercategory.associator_naturality
      (K := K) (𝟙 X') (𝟙 Y') i.iso.hom
  have hEtaInput :
      (η ▷ X) ≫ ((𝟙 X' ⊗ₘ 𝟙 Y') ⊗ₘ i.iso.hom) =
        (𝟙_ C ◁ i.iso.hom) ≫ (η ▷ X') := by
    have hRight :=
      MonoidalSupercategory.super_interchange
        (K := K) (𝟙 (X' ⊗ Y')) i.iso.hom η (𝟙 X)
        i.hom_mem hη
    have hLeft :=
      MonoidalSupercategory.super_interchange
        (K := K) η (𝟙 X') (𝟙 (𝟙_ C)) i.iso.hom
        (Supercategory.id_mem_even X')
        (Supercategory.id_mem_even (𝟙_ C))
    rw [MonoidalSupercategory.whiskerRight_eq (K := K),
      MonoidalSupercategory.whiskerLeft_eq (K := K),
      MonoidalSupercategory.whiskerRight_eq (K := K)]
    rw [MonoidalSupercategory.tensor_id (K := K)]
    calc
      (η ⊗ₘ 𝟙 X) ≫
            (𝟙 (X' ⊗ Y') ⊗ₘ i.iso.hom) =
          η ⊗ₘ i.iso.hom := by
            simpa only [koszulSign, mul_zero, ZMod.val_zero, pow_zero,
              one_smul, Category.id_comp, Category.comp_id] using hRight
      _ = (𝟙 (𝟙_ C) ⊗ₘ i.iso.hom) ≫
            (η ⊗ₘ 𝟙 X') := by
            simpa only [koszulSign, mul_zero, ZMod.val_zero, pow_zero,
              one_smul, Category.id_comp, Category.comp_id] using hLeft.symm
  have hUnitor :
      (λ_ X).inv ≫ (𝟙_ C ◁ i.iso.hom) =
        i.iso.hom ≫ (λ_ X').inv := by
    apply (cancel_mono (λ_ X').hom).mp
    rw [Category.assoc,
      MonoidalSupercategory.leftUnitor_naturality (K := K) i.iso.hom]
    simp
  have hOutputExchange :
      (i.iso.inv ⊗ₘ 𝟙 (Y' ⊗ X')) ≫ (X ◁ ε) =
        (X' ◁ ε) ≫ (i.iso.inv ▷ 𝟙_ C) := by
    have hLeft :=
      MonoidalSupercategory.super_interchange
        (K := K) (𝟙 X) ε i.iso.inv (𝟙 (Y' ⊗ X'))
        hε i.inv_mem
    have hRight :=
      MonoidalSupercategory.super_interchange
        (K := K) i.iso.inv (𝟙 (𝟙_ C)) (𝟙 X') ε
        (Supercategory.id_mem_even (𝟙_ C))
        (Supercategory.id_mem_even X')
    rw [MonoidalSupercategory.whiskerLeft_eq (K := K) X ε,
      MonoidalSupercategory.whiskerLeft_eq (K := K) X' ε,
      MonoidalSupercategory.whiskerRight_eq (K := K)]
    calc
      (i.iso.inv ⊗ₘ 𝟙 (Y' ⊗ X')) ≫
            (𝟙 X ⊗ₘ ε) =
          i.iso.inv ⊗ₘ ε := by
            simpa only [koszulSign, zero_mul, ZMod.val_zero, pow_zero,
              one_smul, Category.id_comp, Category.comp_id] using hLeft
      _ = (𝟙 X' ⊗ₘ ε) ≫
            (i.iso.inv ⊗ₘ 𝟙 (𝟙_ C)) := by
            simpa only [koszulSign, mul_zero, ZMod.val_zero, pow_zero,
              one_smul, Category.id_comp, Category.comp_id] using hRight.symm
  have hRightUnitor :
      (i.iso.inv ▷ 𝟙_ C) ≫ (ρ_ X).hom =
        (ρ_ X').hom ≫ i.iso.inv :=
    MonoidalSupercategory.rightUnitor_naturality
      (K := K) i.iso.inv
  have hRest :
      (λ_ X).inv ≫
          (η ▷ X) ≫ (α_ X' Y' X).hom ≫
            (i.iso.inv ⊗ₘ (𝟙 Y' ⊗ₘ i.iso.hom)) ≫
              (X ◁ ε) ≫ (ρ_ X).hom =
        i.iso.hom ≫ normalizedXSnake η ε ≫ i.iso.inv := by
    rw [← hQFactor]
    slice_lhs 3 4 => rw [← hInputTensor]
    slice_lhs 2 3 => rw [hEtaInput]
    slice_lhs 1 2 => rw [hUnitor]
    slice_lhs 5 6 => rw [hOutputExchange]
    slice_lhs 6 7 => rw [hRightUnitor]
    simp only [normalizedXSnake, Category.assoc]
  change normalizedXSnake (η ≫ T) (J ≫ ε) =
    koszulSign K d d •
      (i.iso.hom ≫ normalizedXSnake η ε ≫ i.iso.inv)
  rw [normalizedXSnake, hCoevalWhisker, hEvalWhisker]
  slice_lhs 3 4 => rw [hTAssociator]
  rw [MonoidalSupercategory.whiskerLeft_eq (K := K) X J]
  slice_lhs 4 5 => rw [hCore]
  simp only [Linear.comp_smul, Linear.smul_comp, Category.assoc]
  rw [hRest]

/-- A scalar multiplying the evaluation multiplies the normalized
`X`-snake by the same scalar. -/
theorem normalizedXSnake_smul_evaluation
    (r : K)
    (η : 𝟙_ C ⟶ X ⊗ Y) (ε : Y ⊗ X ⟶ 𝟙_ C) :
    normalizedXSnake η (r • ε) =
      r • normalizedXSnake η ε := by
  have hWhisker :
      X ◁ (r • ε) = r • (X ◁ ε) := by
    rw [MonoidalSupercategory.whiskerLeft_eq (K := K),
      MonoidalSupercategory.whiskerLeft_eq (K := K)]
    exact MonoidalSupercategory.tensor_smul_right
      (K := K) r (𝟙 X) ε
  rw [normalizedXSnake, hWhisker]
  simp only [Linear.comp_smul, Linear.smul_comp]
  rw [normalizedXSnake]

private theorem koszulSign_mul_self (d : ZMod 2) :
    koszulSign K d d * koszulSign K d d = 1 := by
  rcases zmod2_cases d with hd | hd <;> subst d
  · simp [koszulSign]
  · simp [koszulSign, ZMod.val_one]

/-- The coevaluation obtained by simultaneously transporting both objects
of an exact pairing across homogeneous isomorphisms of the same degree. -/
def simultaneousHomogeneousTransportCoevaluation
    {X' Y' : C} {d : ZMod 2}
    (p : SuperExactPairing K X' Y')
    (i : HomogeneousIso K d X X')
    (j : HomogeneousIso K d Y Y') :
    𝟙_ C ⟶ X ⊗ Y :=
  p.coeval ≫ (i.iso.inv ⊗ₘ j.iso.inv)

/-- The sign-corrected evaluation obtained by simultaneously transporting
both objects of an exact pairing across homogeneous isomorphisms. -/
def simultaneousHomogeneousTransportEvaluation
    {X' Y' : C} {d : ZMod 2}
    (p : SuperExactPairing K X' Y')
    (i : HomogeneousIso K d X X')
    (j : HomogeneousIso K d Y Y') :
    Y ⊗ X ⟶ 𝟙_ C :=
  koszulSign K d d •
    ((j.iso.hom ⊗ₘ i.iso.hom) ≫ p.eval)

/-- The simultaneously transported coevaluation is even. -/
theorem simultaneousHomogeneousTransportCoevaluation_mem
    {X' Y' : C} {d : ZMod 2}
    (p : SuperExactPairing K X' Y')
    (i : HomogeneousIso K d X X')
    (j : HomogeneousIso K d Y Y') :
    simultaneousHomogeneousTransportCoevaluation p i j ∈
      homGrade K (𝟙_ C) (X ⊗ Y) 0 := by
  have hTensor :
      i.iso.inv ⊗ₘ j.iso.inv ∈
        homGrade K (X' ⊗ Y') (X ⊗ Y) 0 := by
    simpa only [ZModModule.add_self] using
      MonoidalSupercategory.tensorHom_mem
        (K := K) i.iso.inv j.iso.inv i.inv_mem j.inv_mem
  simpa only [simultaneousHomogeneousTransportCoevaluation,
    homGrade, zero_add] using
    Supercategory.comp_mem p.coeval
      (i.iso.inv ⊗ₘ j.iso.inv) p.coeval_mem hTensor

/-- The sign-corrected simultaneously transported evaluation is even. -/
theorem simultaneousHomogeneousTransportEvaluation_mem
    {X' Y' : C} {d : ZMod 2}
    (p : SuperExactPairing K X' Y')
    (i : HomogeneousIso K d X X')
    (j : HomogeneousIso K d Y Y') :
    simultaneousHomogeneousTransportEvaluation p i j ∈
      homGrade K (Y ⊗ X) (𝟙_ C) 0 := by
  have hTensor :
      j.iso.hom ⊗ₘ i.iso.hom ∈
        homGrade K (Y ⊗ X) (Y' ⊗ X') 0 := by
    simpa only [ZModModule.add_self] using
      MonoidalSupercategory.tensorHom_mem
        (K := K) j.iso.hom i.iso.hom j.hom_mem i.hom_mem
  have hRaw :
      (j.iso.hom ⊗ₘ i.iso.hom) ≫ p.eval ∈
        homGrade K (Y ⊗ X) (𝟙_ C) 0 := by
    simpa only [homGrade, zero_add] using
      Supercategory.comp_mem
        (j.iso.hom ⊗ₘ i.iso.hom) p.eval hTensor p.eval_mem
  exact Submodule.smul_mem _ _ hRaw

/-- The sign-corrected simultaneous homogeneous transport preserves the
normalized `X`-snake identity. -/
theorem normalizedXSnake_simultaneousHomogeneousTransport
    {X' Y' : C} {d : ZMod 2}
    (p : SuperExactPairing K X' Y')
    (i : HomogeneousIso K d X X')
    (j : HomogeneousIso K d Y Y') :
    normalizedXSnake
        (simultaneousHomogeneousTransportCoevaluation p i j)
        (simultaneousHomogeneousTransportEvaluation p i j) =
      𝟙 X := by
  have hBase :
      normalizedXSnake p.coeval p.eval = 𝟙 X' := by
    calc
      normalizedXSnake p.coeval p.eval =
          (λ_ X').inv ≫
            (p.coeval ▷ X' ≫ (α_ X' Y' X').hom ≫
              X' ◁ p.eval) ≫
                (ρ_ X').hom := by
            simp only [normalizedXSnake, Category.assoc]
      _ = (λ_ X').inv ≫
            ((λ_ X').hom ≫ (ρ_ X').inv) ≫
              (ρ_ X').hom := by
            rw [p.evaluation_coevaluation]
      _ = 𝟙 X' := by simp
  rw [simultaneousHomogeneousTransportEvaluation,
    normalizedXSnake_smul_evaluation]
  rw [simultaneousHomogeneousTransportCoevaluation,
    normalizedXSnake_simultaneous_homogeneous_transport
      p.coeval p.eval i j p.coeval_mem p.eval_mem]
  rw [hBase]
  simp only [smul_smul, koszulSign_mul_self, one_smul,
    Category.id_comp, Iso.hom_inv_id]

namespace SuperExactPairing

/-- Complete a super exact pairing from one normalized snake identity and
the Schur property for nonzero even endomorphisms of the opposite object. -/
def ofNormalizedXSnakeOfEvenSchur
    (η : 𝟙_ C ⟶ X ⊗ Y) (ε : Y ⊗ X ⟶ 𝟙_ C)
    (hη : η ∈ homGrade K (𝟙_ C) (X ⊗ Y) 0)
    (hε : ε ∈ homGrade K (Y ⊗ X) (𝟙_ C) 0)
    (hXSnake : normalizedXSnake η ε = 𝟙 X)
    (hX : 𝟙 X ≠ 0)
    (hSchur : ∀ g : Y ⟶ Y,
      g ∈ homGrade K Y Y 0 → g ≠ 0 → IsIso g) :
    SuperExactPairing K X Y := by
  let η₀ :
      𝟙_ (EvenSubcategory K C) ⟶
        evenObj K C X ⊗ evenObj K C Y :=
    ⟨η, hη⟩
  let ε₀ :
      evenObj K C Y ⊗ evenObj K C X ⟶
        𝟙_ (EvenSubcategory K C) :=
    ⟨ε, hε⟩
  have hXSnake₀ :
      normalizedXSnake η₀ ε₀ = 𝟙 (evenObj K C X) := by
    apply WideSubcategory.hom_ext
    exact hXSnake
  have hη₀ : η₀ ≠ 0 := by
    intro hηzero
    have h := hXSnake₀
    rw [hηzero] at h
    have hid : 𝟙 (evenObj K C X) = 0 := by
      simpa [normalizedXSnake] using h.symm
    exact hX (congrArg (fun f => f.hom) hid)
  let g₀ : evenObj K C Y ⟶ evenObj K C Y :=
    normalizedYSnake η₀ ε₀
  have hg₀ : g₀ ≠ 0 := by
    intro hgzero
    apply hη₀
    have habs :=
      coevaluation_absorbs_normalizedYSnake η₀ ε₀ hXSnake₀
    change η₀ ≫ evenObj K C X ◁ g₀ = η₀ at habs
    rw [hgzero] at habs
    simpa using habs.symm
  have hgHom : g₀.hom ≠ 0 := by
    intro hgzero
    apply hg₀
    apply WideSubcategory.hom_ext
    simpa using hgzero
  letI : IsIso g₀.hom :=
    hSchur g₀.hom g₀.property hgHom
  have hgId : g₀.hom = 𝟙 Y := by
    apply (cancel_epi g₀.hom).mp
    have hidem :=
      normalizedYSnake_idempotent η₀ ε₀ hXSnake₀
    simpa [g₀] using congrArg (fun f => f.hom) hidem
  have hgId₀ : g₀ = 𝟙 (evenObj K C Y) := by
    apply WideSubcategory.hom_ext
    exact hgId
  exact ofEven
    { coevaluation' := η₀
      evaluation' := ε₀
      evaluation_coevaluation' :=
        (normalizedXSnake_eq_id_iff η₀ ε₀).mp hXSnake₀
      coevaluation_evaluation' :=
        (normalizedYSnake_eq_id_iff η₀ ε₀).mp hgId₀ }

/-- Transport both objects of an exact pairing across homogeneous
isomorphisms of one common degree.

The evaluation is corrected by the Koszul self-sign.  One transported snake
is proved directly; the opposite snake follows from the even Schur property
of the transported second object. -/
def congrHomogeneousOfEvenSchur
    {X' Y' : C} {d : ZMod 2}
    (i : HomogeneousIso K d X X')
    (j : HomogeneousIso K d Y Y')
    (p : SuperExactPairing K X' Y')
    (hX : 𝟙 X ≠ 0)
    (hSchur : ∀ g : Y ⟶ Y,
      g ∈ homGrade K Y Y 0 → g ≠ 0 → IsIso g) :
    SuperExactPairing K X Y :=
  ofNormalizedXSnakeOfEvenSchur
    (simultaneousHomogeneousTransportCoevaluation p i j)
    (simultaneousHomogeneousTransportEvaluation p i j)
    (simultaneousHomogeneousTransportCoevaluation_mem p i j)
    (simultaneousHomogeneousTransportEvaluation_mem p i j)
    (normalizedXSnake_simultaneousHomogeneousTransport p i j)
    hX hSchur

end SuperExactPairing

end Super

end

end Superfusion.Category
