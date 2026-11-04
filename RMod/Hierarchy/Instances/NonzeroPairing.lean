import RMod.Hierarchy.Instances.EvenMonoidalLinear
import Mathlib.CategoryTheory.Simple

/-!
# Nonzero coevaluation for a simple object

The triangle identity would force the identity of a simple object to
vanish if its coevaluation were zero. Thus a decomposition of its tensor
product with an exact dual must contain at least one summand.
-/

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped BigOperators
namespace RMod.Legacy

theorem simple_coevaluation_ne_zero {D : Type*} [Category D] [MonoidalCategory D]
    [Preadditive D] [MonoidalPreadditive D] (X Y : D) [Simple X] [ExactPairing X Y] :
    η_ X Y ≠ 0 := by
  intro he
  have h := ExactPairing.evaluation_coevaluation X Y
  rw [he, MonoidalPreadditive.zero_whiskerRight, zero_comp] at h
  apply id_nonzero X
  calc
    𝟙 X = (λ_ X).inv ≫ ((λ_ X).hom ≫ (ρ_ X).inv) ≫ (ρ_ X).hom := by simp
    _ = (λ_ X).inv ≫ 0 ≫ (ρ_ X).hom := by rw [← h]
    _ = 0 := by simp

theorem simple_pairing_nonempty_biproduct {D : Type*} [Category D] [MonoidalCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    (X Y : D) [Simple X] [ExactPairing X Y] {J : Type} [Fintype J]
    (S : J → D) (e : X ⊗ Y ≅ ⨁ S) : Nonempty J := by
  classical
  by_contra hJ
  haveI : IsEmpty J := not_nonempty_iff.mp hJ
  have hid : 𝟙 (biproduct S) = 0 := by
    exact (biproduct.total (f := S)).symm.trans (Finset.sum_eq_zero fun j _ => isEmptyElim j)
  apply simple_coevaluation_ne_zero X Y
  apply (cancel_mono e.hom).mp
  rw [zero_comp]
  calc
    η_ X Y ≫ e.hom = (η_ X Y ≫ e.hom) ≫ 𝟙 _ := (Category.comp_id _).symm
    _ = 0 := by rw [hid, comp_zero]

end RMod.Legacy
