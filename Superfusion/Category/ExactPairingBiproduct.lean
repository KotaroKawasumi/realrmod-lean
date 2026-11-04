import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Superfusion.Category.SuperBiproduct

/-!
# Finite biproducts of exact pairings

This file proves that a finite family of exact pairings induces an exact
pairing between the corresponding biproducts.  The coevaluation and
evaluation are the diagonal sums of the component maps.  The two snake
identities are checked entrywise using the biproduct distributors.

The final definition applies this result in the even core of a monoidal
supercategory.  It propagates already supplied componentwise super exact
pairings; it does not construct pairings for the regular atoms.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe v u

namespace CategoryTheory.ExactPairing

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [MonoidalCategory C] [MonoidalPreadditive C] [HasFiniteBiproducts C]

set_option autoImplicit false in
/-- A finite family of exact pairings indexed by a universe-zero type induces
an exact pairing between the corresponding biproducts. -/
@[implicit_reducible]
noncomputable def biproduct
    {J : Type} [Finite J]
    {X Y : J → C}
    (p : ∀ j, ExactPairing (X j) (Y j)) :
    ExactPairing (⨁ X) (⨁ Y) := by
  classical
  letI : Fintype J := Fintype.ofFinite J
  let coevaluation :
      𝟙_ C ⟶ (⨁ X) ⊗ (⨁ Y) :=
    ∑ j, (p j).coevaluation' ≫
      (biproduct.ι X j ⊗ₘ biproduct.ι Y j)
  let evaluation :
      (⨁ Y) ⊗ (⨁ X) ⟶ 𝟙_ C :=
    ∑ j, (biproduct.π Y j ⊗ₘ biproduct.π X j) ≫
      (p j).evaluation'
  have left_component (a b j k : J) :
      (biproduct.ι Y j ▷ 𝟙_ C) ≫
        (⨁ Y) ◁ ((p b).coevaluation' ≫
          (biproduct.ι X b ⊗ₘ biproduct.ι Y b)) ≫
        (α_ (⨁ Y) (⨁ X) (⨁ Y)).inv ≫
        (((biproduct.π Y a ⊗ₘ biproduct.π X a) ≫
          (p a).evaluation') ▷ (⨁ Y)) ≫
        𝟙_ C ◁ biproduct.π Y k =
      Y j ◁ (p b).coevaluation' ≫
        ((biproduct.ι Y j ≫ biproduct.π Y a) ▷
          (X b ⊗ Y b)) ≫
        (Y a ◁ ((biproduct.ι X b ≫ biproduct.π X a) ▷
          Y b)) ≫
        (Y a ◁ (X a ◁
          (biproduct.ι Y b ≫ biproduct.π Y k))) ≫
        (α_ (Y a) (X a) (Y k)).inv ≫
        (p a).evaluation' ▷ Y k := by
    calc
      _ = ((biproduct.ι Y j ▷ 𝟙_ C) ≫
            (⨁ Y) ◁ (p b).coevaluation') ⊗≫
          ((⨁ Y) ◁
            (biproduct.ι X b ⊗ₘ biproduct.ι Y b)) ⊗≫
          ((biproduct.π Y a ⊗ₘ biproduct.π X a) ▷
            (⨁ Y)) ⊗≫
          ((p a).evaluation' ▷ (⨁ Y)) ⊗≫
          (𝟙_ C ◁ biproduct.π Y k) := by
            monoidal
      _ = (Y j ◁ (p b).coevaluation' ≫
            biproduct.ι Y j ▷ (X b ⊗ Y b)) ⊗≫
          ((⨁ Y) ◁
            (biproduct.ι X b ⊗ₘ biproduct.ι Y b)) ⊗≫
          ((biproduct.π Y a ⊗ₘ biproduct.π X a) ▷
            (⨁ Y)) ⊗≫
          ((p a).evaluation' ▷ (⨁ Y)) ⊗≫
          (𝟙_ C ◁ biproduct.π Y k) := by
            rw [← whisker_exchange]
      _ = Y j ◁ (p b).coevaluation' ⊗≫
          (biproduct.ι Y j ▷ (X b ⊗ Y b)) ⊗≫
          (((⨁ Y) ◁
              (biproduct.ι X b ⊗ₘ biproduct.ι Y b)) ≫
            biproduct.π Y a ▷ ((⨁ X) ⊗ (⨁ Y))) ⊗≫
          (Y a ◁ (biproduct.π X a ▷ (⨁ Y))) ⊗≫
          ((p a).evaluation' ▷ (⨁ Y)) ⊗≫
          (𝟙_ C ◁ biproduct.π Y k) := by
            simp only [tensorHom_def, comp_whiskerRight]
            monoidal
      _ = Y j ◁ (p b).coevaluation' ⊗≫
          (biproduct.ι Y j ▷ (X b ⊗ Y b)) ⊗≫
          (biproduct.π Y a ▷ (X b ⊗ Y b) ≫
            Y a ◁
              (biproduct.ι X b ⊗ₘ biproduct.ι Y b)) ⊗≫
          (Y a ◁ (biproduct.π X a ▷ (⨁ Y))) ⊗≫
          ((p a).evaluation' ▷ (⨁ Y)) ⊗≫
          (𝟙_ C ◁ biproduct.π Y k) := by
            rw [whisker_exchange]
      _ = Y j ◁ (p b).coevaluation' ⊗≫
          ((biproduct.ι Y j ≫ biproduct.π Y a) ▷
            (X b ⊗ Y b)) ⊗≫
          (Y a ◁ (biproduct.ι X b ▷ Y b)) ⊗≫
          (Y a ◁ ((⨁ X) ◁ biproduct.ι Y b ≫
            biproduct.π X a ▷ (⨁ Y))) ⊗≫
          ((p a).evaluation' ▷ (⨁ Y)) ⊗≫
          (𝟙_ C ◁ biproduct.π Y k) := by
            simp only [tensorHom_def, whiskerLeft_comp]
            monoidal
      _ = Y j ◁ (p b).coevaluation' ⊗≫
          ((biproduct.ι Y j ≫ biproduct.π Y a) ▷
            (X b ⊗ Y b)) ⊗≫
          (Y a ◁ (biproduct.ι X b ▷ Y b)) ⊗≫
          (Y a ◁ (biproduct.π X a ▷ Y b ≫
            X a ◁ biproduct.ι Y b)) ⊗≫
          ((p a).evaluation' ▷ (⨁ Y)) ⊗≫
          (𝟙_ C ◁ biproduct.π Y k) := by
            rw [whisker_exchange]
      _ = Y j ◁ (p b).coevaluation' ⊗≫
          ((biproduct.ι Y j ≫ biproduct.π Y a) ▷
            (X b ⊗ Y b)) ⊗≫
          (Y a ◁ ((biproduct.ι X b ≫
            biproduct.π X a) ▷ Y b)) ⊗≫
          ((Y a ⊗ X a) ◁ biproduct.ι Y b) ⊗≫
          (((p a).evaluation' ▷ (⨁ Y)) ≫
            𝟙_ C ◁ biproduct.π Y k) := by
              monoidal
      _ = _ := by
        rw [← whisker_exchange]
        monoidal
  have right_component (a b j k : J) :
      (𝟙_ C ◁ biproduct.ι X j) ≫
        (((p b).coevaluation' ≫
          (biproduct.ι X b ⊗ₘ biproduct.ι Y b)) ▷
            (⨁ X)) ≫
        (α_ (⨁ X) (⨁ Y) (⨁ X)).hom ≫
        (⨁ X) ◁
          ((biproduct.π Y a ⊗ₘ biproduct.π X a) ≫
            (p a).evaluation') ≫
        (biproduct.π X k ▷ 𝟙_ C) =
      (p b).coevaluation' ▷ X j ≫
        (α_ (X b) (Y b) (X j)).hom ≫
        (X b ◁ (Y b ◁
          (biproduct.ι X j ≫ biproduct.π X a))) ≫
        ((biproduct.ι X b ≫ biproduct.π X k) ▷
          (Y b ⊗ X a)) ≫
        (X k ◁ ((biproduct.ι Y b ≫ biproduct.π Y a) ▷
          X a)) ≫
        X k ◁ (p a).evaluation' := by
    calc
      _ = ((𝟙_ C ◁ biproduct.ι X j) ≫
            (p b).coevaluation' ▷ (⨁ X)) ⊗≫
          ((biproduct.ι X b ⊗ₘ biproduct.ι Y b) ▷
            (⨁ X)) ⊗≫
          ((⨁ X) ◁
            (biproduct.π Y a ⊗ₘ biproduct.π X a)) ⊗≫
          ((⨁ X) ◁ (p a).evaluation') ⊗≫
          (biproduct.π X k ▷ 𝟙_ C) := by
            monoidal
      _ = ((p b).coevaluation' ▷ X j ≫
            (X b ⊗ Y b) ◁ biproduct.ι X j) ⊗≫
          ((biproduct.ι X b ⊗ₘ biproduct.ι Y b) ▷
            (⨁ X)) ⊗≫
          ((⨁ X) ◁
            (biproduct.π Y a ⊗ₘ biproduct.π X a)) ⊗≫
          ((⨁ X) ◁ (p a).evaluation') ⊗≫
          (biproduct.π X k ▷ 𝟙_ C) := by
            rw [whisker_exchange]
      _ = (p b).coevaluation' ▷ X j ⊗≫
          ((X b ⊗ Y b) ◁ biproduct.ι X j) ⊗≫
          ((((biproduct.ι X b ⊗ₘ biproduct.ι Y b) ≫
              (⨁ X) ◁ biproduct.π Y a) ▷ (⨁ X)) ≫
            ((⨁ X) ⊗ Y a) ◁ biproduct.π X a) ⊗≫
          ((⨁ X) ◁ (p a).evaluation') ⊗≫
          (biproduct.π X k ▷ 𝟙_ C) := by
            simp only [tensorHom_def, whiskerLeft_comp]
            monoidal
      _ = (p b).coevaluation' ▷ X j ⊗≫
          ((X b ⊗ Y b) ◁ biproduct.ι X j) ⊗≫
          ((X b ⊗ Y b) ◁ biproduct.π X a ≫
            (((biproduct.ι X b ⊗ₘ biproduct.ι Y b) ≫
              (⨁ X) ◁ biproduct.π Y a) ▷ X a)) ⊗≫
          ((⨁ X) ◁ (p a).evaluation') ⊗≫
          (biproduct.π X k ▷ 𝟙_ C) := by
            rw [← whisker_exchange]
      _ = (p b).coevaluation' ▷ X j ⊗≫
          (X b ◁ (Y b ◁
            (biproduct.ι X j ≫ biproduct.π X a))) ⊗≫
          ((biproduct.ι X b ▷ Y b) ▷ X a) ⊗≫
          ((⨁ X) ◁
            ((biproduct.ι Y b ≫ biproduct.π Y a) ▷
              X a)) ⊗≫
          ((⨁ X) ◁ (p a).evaluation') ⊗≫
          (biproduct.π X k ▷ 𝟙_ C) := by
            simp only [tensorHom_def, comp_whiskerRight,
              whiskerLeft_comp]
            monoidal
      _ = (p b).coevaluation' ▷ X j ⊗≫
          (X b ◁ (Y b ◁
            (biproduct.ι X j ≫ biproduct.π X a))) ⊗≫
          (biproduct.ι X b ▷ (Y b ⊗ X a)) ⊗≫
          (((⨁ X) ◁
              (((biproduct.ι Y b ≫ biproduct.π Y a) ▷
                X a) ≫ (p a).evaluation')) ≫
            biproduct.π X k ▷ 𝟙_ C) := by
            monoidal
      _ = (p b).coevaluation' ▷ X j ⊗≫
          (X b ◁ (Y b ◁
            (biproduct.ι X j ≫ biproduct.π X a))) ⊗≫
          (biproduct.ι X b ▷ (Y b ⊗ X a)) ⊗≫
          ((biproduct.π X k ▷ (Y b ⊗ X a)) ≫
            X k ◁
              (((biproduct.ι Y b ≫ biproduct.π Y a) ▷
                X a) ≫ (p a).evaluation')) := by
            rw [whisker_exchange]
      _ = _ := by
        simp only [comp_whiskerRight, whiskerLeft_comp]
        monoidal
  exact
    { coevaluation' := coevaluation
      evaluation' := evaluation
      coevaluation_evaluation' := by
        apply rightDistributor_ext_left
        intro j
        apply leftDistributor_ext_right
        intro k
        simp only [coevaluation, evaluation, whiskerLeft_sum,
          sum_whiskerRight, Preadditive.comp_sum,
          Preadditive.sum_comp, Category.assoc]
        simp_rw [left_component]
        rw [Finset.sum_eq_single j]
        · rw [Finset.sum_eq_single j]
          · by_cases h : j = k
            · subst k
              simpa [biproduct.ι_π] using
                (p j).coevaluation_evaluation'
            · simp [h]
          · intro b hb hbj
            simp [biproduct.ι_π, hbj]
          · simp
        · intro a ha haj
          have hja : j ≠ a := Ne.symm haj
          simp [biproduct.ι_π, hja]
        · simp
      evaluation_coevaluation' := by
        apply leftDistributor_ext_left
        intro j
        apply rightDistributor_ext_right
        intro k
        simp only [coevaluation, evaluation, whiskerLeft_sum,
          sum_whiskerRight, Preadditive.comp_sum,
          Preadditive.sum_comp, Category.assoc]
        simp_rw [right_component]
        rw [Finset.sum_eq_single j]
        · rw [Finset.sum_eq_single j]
          · by_cases h : j = k
            · subst k
              simpa [biproduct.ι_π] using
                (p j).evaluation_coevaluation'
            · simp [h]
          · intro b hb hbj
            simp [biproduct.ι_π, hbj]
          · simp
        · intro a ha haj
          have hja : j ≠ a := Ne.symm haj
          simp [biproduct.ι_π, hja]
        · simp }

end CategoryTheory.ExactPairing

namespace Superfusion.Category.SuperExactPairing

variable {K : Type*} [Field K]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear K C]
  [Supercategory K C] [MonoidalCategoryStruct C]
  [MonoidalSupercategory K C]
  [HasFiniteBiproducts (EvenSubcategory K C)]
variable {J : Type} [Finite J]
variable {X Y : J → C}

/-- The super-biproducts of componentwise super exact pairings are
super exactly paired. -/
@[implicit_reducible]
noncomputable def biproduct
    (p : ∀ j, SuperExactPairing K (X j) (Y j)) :
    SuperExactPairing K
      (superBiproduct (K := K) X)
      (superBiproduct (K := K) Y) :=
  ofEven (CategoryTheory.ExactPairing.biproduct
    (fun j => (p j).toEven))

end Superfusion.Category.SuperExactPairing
