import RMod.Enriched.TotalNaturality

/-! Total-vector equations recover full Hom-object naturality: single-degree
vectors detect each component, and pure tensors generate tensor Hom objects. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open GradedObject.Monoidal
open scoped BigOperators TensorProduct
universe u
namespace RMod.EnrichedSupport
open Regression

/-- Equality on total vectors detects equality of graded linear maps. -/
theorem total_ext {A B : SuperVec} {f g : A ⟶ B}
    (h : ∀ x : ∀ a, A a, ∀ a, f a (x a) = g a (x a)) : f = g := by
  classical
  funext a
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  simpa using h (Pi.single a x) a

/-- A total naturality equation implies the corresponding Hom-object equation. -/
theorem hom_equation_of_total {D : Type u} [SuperCategory D]
    {H : SuperVec} {A B A' B' : Even D}
    (f : H ⟶ SHom D A B) (g : H ⟶ SHom D A' B') (a : A ⟶ A') (b : B ⟶ B')
    (h : ∀ p : ∀ r, H r,
      tComp D (fun r => f r (p r)) (evenPoint (ForgetEnrichment.homTo SuperVec b)) =
        tComp D (evenPoint (ForgetEnrichment.homTo SuperVec a)) (fun r => g r (p r))) :
    f ≫ eHomWhiskerLeft SuperVec A b = g ≫ eHomWhiskerRight SuperVec a B' := by
  apply total_ext
  intro p r
  have hr := congrFun (h p) r
  rw [← post_apply, ← pre_apply] at hr
  exact hr

/-- Supported vectors recover every homogeneous pure tensor. -/
theorem tensorPoint_single {A B : SuperVec} (i j : ZMod 2) (x : A i) (y : B j) :
    tensorPoint (Pi.single i x) (Pi.single j y) (i + j) =
      ιTensorObj A B i j (i + j) rfl (x ⊗ₜ[ℝ] y) := by
  classical
  unfold tensorPoint
  rw [Finset.sum_eq_single i]
  · simp only [Pi.single_eq_same]
    have aux (k : ZMod 2) (hk : k = j) :
        ιTensorObj A B i k (i + j) (by rw [hk]) (x ⊗ₜ[ℝ] Pi.single (M := fun a => B a) j y k) =
          ιTensorObj A B i j (i + j) rfl (x ⊗ₜ[ℝ] y) := by
      subst k
      rw [Pi.single_eq_same]
    exact aux (i + j - i) (by abel)
  · intro k _ hki
    simp [Pi.single_eq_of_ne hki]
  · simp

/-- The convolution tensor points span all graded tensor components. -/
theorem tensorPoint_ext {A B H : SuperVec} {f g : A ⊗ B ⟶ H}
    (h : ∀ (x : ∀ a, A a) (y : ∀ a, B a) (a : ZMod 2),
      f a (tensorPoint x y a) = g a (tensorPoint x y a)) : f = g := by
  funext a
  apply tensorObj_ext
  intro i j hij
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  subst a
  change f (i + j) (ιTensorObj A B i j (i + j) rfl (x ⊗ₜ[ℝ] y)) =
    g (i + j) (ιTensorObj A B i j (i + j) rfl (x ⊗ₜ[ℝ] y))
  simpa only [tensorPoint_single] using
    h (Pi.single i x) (Pi.single j y) (i + j)

end RMod.EnrichedSupport

namespace RMod.EnrichedSupport
open Regression GradedObject.Monoidal

/-- A tensor of supported points is supported in the sum of their degrees. -/
theorem tensorPoint_single_full {A B : SuperVec} (i j : ZMod 2) (x : A i) (y : B j) :
    tensorPoint (Pi.single i x) (Pi.single j y) =
      Pi.single (i + j) (ιTensorObj A B i j (i + j) rfl (x ⊗ₜ[ℝ] y)) := by
  classical
  funext a
  by_cases ha : a = i + j
  · subst a
    simp [tensorPoint_single]
  · rw [Pi.single_eq_of_ne ha]
    unfold tensorPoint
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : k = i
    · subst k
      have hj : a - i ≠ j := by
        intro h
        exact ha ((sub_eq_iff_eq_add.mp h).trans (add_comm j i))
      simp [Pi.single_eq_of_ne hj]
    · simp [Pi.single_eq_of_ne hk]

/-- Nested convolution points detect equality on a threefold tensor Hom object. -/
theorem tensorPoint_ext_three {A B C H : SuperVec} {f g : (A ⊗ B) ⊗ C ⟶ H}
    (h : ∀ (x : ∀ a, A a) (y : ∀ a, B a) (z : ∀ a, C a) (a : ZMod 2),
      f a (tensorPoint (tensorPoint x y) z a) = g a (tensorPoint (tensorPoint x y) z a)) :
    f = g := by
  funext a
  apply tensorObj₃'_ext
  intro i j k hij
  apply ModuleCat.hom_ext
  apply TensorProduct.ext_threefold
  intro x y z
  subst a
  have hh := h (Pi.single i x) (Pi.single j y) (Pi.single k z) (i + j + k)
  rw [tensorPoint_single_full, tensorPoint_single] at hh
  exact hh

end RMod.EnrichedSupport

namespace RMod.EnrichedSupport
open Regression

theorem hom_equation_of_tensor {D : Type u} [SuperCategory D]
    {H K : SuperVec} {A B A' B' : Even D}
    (f : H ⊗ K ⟶ SHom D A B) (g : H ⊗ K ⟶ SHom D A' B') (a : A ⟶ A') (b : B ⟶ B')
    (h : ∀ (x : ∀ r, H r) (y : ∀ r, K r),
      tComp D (fun r => f r (tensorPoint x y r)) (evenPoint (ForgetEnrichment.homTo SuperVec b)) =
        tComp D (evenPoint (ForgetEnrichment.homTo SuperVec a)) (fun r => g r (tensorPoint x y r))) :
    f ≫ eHomWhiskerLeft SuperVec A b = g ≫ eHomWhiskerRight SuperVec a B' := by
  apply tensorPoint_ext
  intro x y r
  have hr := congrFun (h x y) r
  rw [← post_apply, ← pre_apply] at hr
  exact hr

theorem hom_equation_of_triple {D : Type u} [SuperCategory D]
    {H K L : SuperVec} {A B A' B' : Even D}
    (f : (H ⊗ K) ⊗ L ⟶ SHom D A B) (g : (H ⊗ K) ⊗ L ⟶ SHom D A' B')
    (a : A ⟶ A') (b : B ⟶ B')
    (h : ∀ (x : ∀ r, H r) (y : ∀ r, K r) (z : ∀ r, L r),
      tComp D (fun r => f r (tensorPoint (tensorPoint x y) z r)) (evenPoint (ForgetEnrichment.homTo SuperVec b)) =
        tComp D (evenPoint (ForgetEnrichment.homTo SuperVec a)) (fun r => g r (tensorPoint (tensorPoint x y) z r))) :
    f ≫ eHomWhiskerLeft SuperVec A b = g ≫ eHomWhiskerRight SuperVec a B' := by
  apply tensorPoint_ext_three
  intro x y z r
  have hr := congrFun (h x y z) r
  rw [← post_apply, ← pre_apply] at hr
  exact hr

end RMod.EnrichedSupport
