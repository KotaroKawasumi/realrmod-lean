import Superfusion.Category.ExactPairingCompletion
import Superfusion.Category.WeaklyPointed

/-!
# Detecting a nonzero snake coordinate

A split even coevaluation cannot contract trivially against every
homogeneous unit coordinate of a supermultiplicity decomposition of the
reversed tensor product.  The proof uses the coordinate resolution of the
identity and the ordinary sign-free interchange instances in which one
crossed morphism is an identity.  It chooses no basis.
-/

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace Superfusion.Category

noncomputable section

variable {K : Type*} [Field K]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear K C]
  [Supercategory K C] [MonoidalCategoryStruct C]
  [MonoidalSupercategory K C]

include K

private lemma tensor_zero_right_raw
    {A B D E : C} (f : A ⟶ B) :
    f ⊗ₘ (0 : D ⟶ E) = 0 := by
  have h := MonoidalSupercategory.tensor_add_right
    (K := K) f (0 : D ⟶ E) 0
  simp only [zero_add] at h
  apply add_left_cancel (a := f ⊗ₘ (0 : D ⟶ E))
  simpa using h.symm

private lemma tensor_finset_sum_right_raw
    {ι : Type*} {A B D E : C} (f : A ⟶ B)
    (s : Finset ι) (g : ι → (D ⟶ E)) :
    f ⊗ₘ (∑ i ∈ s, g i) = ∑ i ∈ s, f ⊗ₘ g i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact tensor_zero_right_raw (K := K) f
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      rw [MonoidalSupercategory.tensor_add_right (K := K), ih]

variable [HasFiniteBiproducts (EvenSubcategory K C)]

/-- A split even tensor element has a nonzero contraction against at least
one homogeneous unit coordinate of any supermultiplicity decomposition of
the reversed tensor product. -/
theorem exists_normalizedXSnake_projection_ne_zero
    {X Y : C} {p q : ℕ}
    (η : 𝟙_ C ⟶ X ⊗ Y) (π : X ⊗ Y ⟶ 𝟙_ C)
    (hη : η ∈ homGrade K (𝟙_ C) (X ⊗ Y) 0)
    (hsplit : η ≫ π = 𝟙 (𝟙_ C))
    (m : SuperMultiplicityWitness K C (Y ⊗ X) (𝟙_ C) p q)
    (hX : 𝟙 X ≠ 0) :
    ∃ i : SuperIndex p q,
      normalizedXSnake η (m.projection i) ≠ 0 := by
  classical
  by_contra hexists
  have hzero : ∀ i : SuperIndex p q,
      normalizedXSnake η (m.projection i) = 0 := by
    intro i
    exact not_ne_iff.mp (not_exists.mp hexists i)
  have hcomponent : ∀ i : SuperIndex p q,
      η ▷ X ≫ (α_ X Y X).hom ≫
          X ◁ (m.projection i ≫ m.inclusion i) = 0 := by
    intro i
    have hcontraction :
        η ▷ X ≫ (α_ X Y X).hom ≫
          X ◁ m.projection i = 0 := by
      rw [← cancel_epi (λ_ X).inv, ← cancel_mono (ρ_ X).hom]
      simpa only [normalizedXSnake, Category.assoc,
        Limits.zero_comp, Limits.comp_zero] using hzero i
    have hwhisker :
        (X ◁ m.projection i) ≫ (X ◁ m.inclusion i) =
          X ◁ (m.projection i ≫ m.inclusion i) := by
      have h :=
        MonoidalSupercategory.super_interchange
          (K := K)
          (𝟙 X) (m.inclusion i) (𝟙 X) (m.projection i)
          (m.inclusion_mem i)
          (Supercategory.id_mem_even X)
      rw [MonoidalSupercategory.whiskerLeft_eq (K := K),
        MonoidalSupercategory.whiskerLeft_eq (K := K),
        MonoidalSupercategory.whiskerLeft_eq (K := K)]
      simpa only [
        Category.comp_id, koszulSign, mul_zero, ZMod.val_zero,
        pow_zero, one_smul] using h
    calc
      η ▷ X ≫ (α_ X Y X).hom ≫
            X ◁ (m.projection i ≫ m.inclusion i) =
          (η ▷ X ≫ (α_ X Y X).hom ≫ X ◁ m.projection i) ≫
            X ◁ m.inclusion i := by
              rw [← hwhisker]
              simp only [Category.assoc]
      _ = 0 := by rw [hcontraction, Limits.zero_comp]
  have hwhiskerTotal :
      ∑ i : SuperIndex p q,
          X ◁ (m.projection i ≫ m.inclusion i) =
        𝟙 (X ⊗ (Y ⊗ X)) := by
    simp_rw [MonoidalSupercategory.whiskerLeft_eq (K := K)]
    rw [← tensor_finset_sum_right_raw
      (K := K) (𝟙 X) Finset.univ
      (fun i : SuperIndex p q =>
        m.projection i ≫ m.inclusion i)]
    rw [m.projection_inclusion_total]
    exact MonoidalSupercategory.tensor_id (K := K) X (Y ⊗ X)
  have hηassoc :
      η ▷ X ≫ (α_ X Y X).hom = 0 := by
    calc
      η ▷ X ≫ (α_ X Y X).hom =
          (η ▷ X ≫ (α_ X Y X).hom) ≫
            𝟙 (X ⊗ (Y ⊗ X)) := by simp
      _ = (η ▷ X ≫ (α_ X Y X).hom) ≫
            ∑ i : SuperIndex p q,
              X ◁ (m.projection i ≫ m.inclusion i) := by
            rw [hwhiskerTotal]
      _ = ∑ i : SuperIndex p q,
            (η ▷ X ≫ (α_ X Y X).hom) ≫
              X ◁ (m.projection i ≫ m.inclusion i) := by
            rw [Preadditive.comp_sum]
      _ = 0 := by
            exact Finset.sum_eq_zero (fun i _ => by
              simpa only [Category.assoc] using hcomponent i)
  have hηwhisker : η ▷ X = 0 := by
    apply (cancel_mono (α_ X Y X).hom).mp
    simpa only [Limits.zero_comp] using hηassoc
  have hsplitWhisker :
      (η ▷ X) ≫ (π ▷ X) = 𝟙 (𝟙_ C ⊗ X) := by
    have h :=
      MonoidalSupercategory.super_interchange
        (K := K)
        π (𝟙 X) η (𝟙 X)
        (Supercategory.id_mem_even X) hη
    calc
      (η ▷ X) ≫ (π ▷ X) =
          (η ≫ π) ⊗ₘ (𝟙 X ≫ 𝟙 X) := by
            rw [MonoidalSupercategory.whiskerRight_eq (K := K),
              MonoidalSupercategory.whiskerRight_eq (K := K)]
            simpa only [
              koszulSign, mul_zero, ZMod.val_zero, pow_zero,
              one_smul] using h
      _ = 𝟙 (𝟙_ C) ⊗ₘ 𝟙 X := by rw [hsplit, Category.comp_id]
      _ = 𝟙 (𝟙_ C ⊗ X) :=
        MonoidalSupercategory.tensor_id (K := K) (𝟙_ C) X
  have hidTensor : 𝟙 (𝟙_ C ⊗ X) = 0 := by
    rw [← hsplitWhisker, hηwhisker, Limits.zero_comp]
  have hleftUnitor : (λ_ X).hom = 0 := by
    rw [← Category.id_comp (λ_ X).hom, hidTensor,
      Limits.zero_comp]
  apply hX
  rw [← (λ_ X).inv_hom_id, hleftUnitor, Limits.comp_zero]

end

end Superfusion.Category
