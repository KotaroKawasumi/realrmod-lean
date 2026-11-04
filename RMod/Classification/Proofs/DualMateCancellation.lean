import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Monoidal.Preadditive

/-!
# Cancellation and isomorphism reflection for the existing dual mates

Mathlib's two tensor Hom equivalences show that opposite mates cancel
when the same exact pairing supplies both dual objects. Its composition
law then makes the mate of an isomorphism invertible. These facts allow
the Schur property to pass to the opposite member of an exact pairing.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification.DualMate

open CategoryTheory MonoidalCategory

variable {V : Type u} [Category.{v} V] [MonoidalCategory V]

theorem right_left {Y : V} [HasLeftDual Y] (f : Y ⟶ Y) :
    (ᘁf)ᘁ = f := by
  have he : η_ (ᘁY) Y ≫ (ᘁY) ◁ ((ᘁf)ᘁ) = η_ (ᘁY) Y ≫ (ᘁY) ◁ f := by
    exact (coevaluation_comp_rightAdjointMate (ᘁf)).trans (coevaluation_comp_leftAdjointMate f)
  have hh := congrArg ((tensorLeftHomEquiv (𝟙_ V) (ᘁY) Y Y).symm) he
  simp only [tensorLeftHomEquiv_symm_coevaluation_comp_whiskerLeft] at hh
  exact (cancel_epi (ρ_ Y).hom).mp hh

theorem left_right {X : V} [HasRightDual X] (f : X ⟶ X) :
    (ᘁ(fᘁ)) = f := by
  have he : η_ X (Xᘁ) ≫ (ᘁ(fᘁ)) ▷ (Xᘁ) = η_ X (Xᘁ) ≫ f ▷ (Xᘁ) := by
    exact (coevaluation_comp_leftAdjointMate (fᘁ)).trans (coevaluation_comp_rightAdjointMate f)
  have hh := congrArg ((tensorRightHomEquiv (𝟙_ V) X (Xᘁ) X).symm) he
  simp only [tensorRightHomEquiv_symm_coevaluation_comp_whiskerRight] at hh
  exact (cancel_epi (λ_ X).hom).mp hh

theorem right_mate_isIso {X : V} [HasRightDual X] (f : X ⟶ X) [IsIso f] :
    IsIso (fᘁ) := by
  refine ⟨⟨(inv f)ᘁ, ?_, ?_⟩⟩
  · rw [← comp_rightAdjointMate, IsIso.inv_hom_id, rightAdjointMate_id]
  · rw [← comp_rightAdjointMate, IsIso.hom_inv_id, rightAdjointMate_id]

theorem left_mate_reflects_isIso {Y : V} [HasLeftDual Y] (f : Y ⟶ Y)
    [IsIso (ᘁf)] : IsIso f := by
  have h := right_mate_isIso (ᘁf)
  rw [right_left f] at h
  exact h

theorem left_mate_isIso {Y : V} [HasLeftDual Y] (f : Y ⟶ Y) [IsIso f] :
    IsIso (ᘁf) := by
  refine ⟨⟨ᘁ(inv f), ?_, ?_⟩⟩
  · rw [← comp_leftAdjointMate, IsIso.inv_hom_id, leftAdjointMate_id]
  · rw [← comp_leftAdjointMate, IsIso.hom_inv_id, leftAdjointMate_id]

theorem right_mate_reflects_isIso {X : V} [HasRightDual X] (f : X ⟶ X)
    [IsIso (fᘁ)] : IsIso f := by
  have h := left_mate_isIso (fᘁ)
  rw [left_right f] at h
  exact h

variable [Preadditive V] [MonoidalPreadditive V]

theorem left_mate_ne_zero {Y : V} [HasLeftDual Y] {f : Y ⟶ Y} (hf : f ≠ 0) :
    (ᘁf) ≠ 0 := by
  intro h
  apply hf
  calc
    f = (ᘁf)ᘁ := (right_left f).symm
    _ = 0 := by rw [h]; simp [rightAdjointMate]

theorem right_mate_ne_zero {X : V} [HasRightDual X] {f : X ⟶ X} (hf : f ≠ 0) :
    (fᘁ) ≠ 0 := by
  intro h
  apply hf
  calc
    f = ᘁ(fᘁ) := (left_right f).symm
    _ = 0 := by rw [h]; simp [leftAdjointMate]

end RMod.Classification.DualMate
