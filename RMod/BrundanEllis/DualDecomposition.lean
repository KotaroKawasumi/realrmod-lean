import Mathlib

/-! Mathlib duals and biproducts express a decomposition independently of choices.
The public weak-invertibility condition can use the selected right dual and two
separate finite sums; the existing proof library uses an existential pairing. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
universe u v
namespace RMod.BrundanEllis.MathlibBridge
attribute [local instance] hasBinaryBiproducts_of_finite_biproducts
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasFiniteBiproducts C]

/-- Group the two parts of a sum-indexed biproduct into a binary biproduct. -/
def sumBiproductIso {p q : ℕ} (F : Fin p → C) (G : Fin q → C) :
    (⨁ Sum.elim F G) ≅ (⨁ F) ⊞ (⨁ G) where
  hom := biproduct.desc (f := Sum.elim F G) fun k => match k with
    | Sum.inl i => biproduct.ι F i ≫ biprod.inl
    | Sum.inr j => biproduct.ι G j ≫ biprod.inr
  inv := biprod.desc
    (biproduct.desc (f := F) fun i => biproduct.ι (Sum.elim F G) (Sum.inl i))
    (biproduct.desc (f := G) fun j => biproduct.ι (Sum.elim F G) (Sum.inr j))
  hom_inv_id := by
    apply biproduct.hom_ext'
    intro k
    cases k <;> simp
  inv_hom_id := by
    apply biprod.hom_ext'
    · apply biproduct.hom_ext'
      intro i
      simp
    · apply biproduct.hom_ext'
      intro j
      simp

variable [MonoidalCategory C]

/-- Choosing the right dual and grouping the sums does not change the property. -/
theorem chosenRightDualDecomposition_iff (X P : C) [HasRightDual X] :
    (∃ p q : ℕ, Nonempty (X ⊗ Xᘁ ≅
      (⨁ fun _ : Fin p => 𝟙_ C) ⊞ (⨁ fun _ : Fin q => P))) ↔
    ∃ Y : C, Nonempty (ExactPairing X Y) ∧
      ∃ p q : ℕ, Nonempty (X ⊗ Y ≅ ⨁ Sum.elim
        (fun _ : Fin p => 𝟙_ C) (fun _ : Fin q => P)) := by
  constructor
  · rintro ⟨p, q, ⟨e⟩⟩
    exact ⟨Xᘁ, ⟨inferInstance⟩, p, q,
      ⟨e ≪≫ (sumBiproductIso (fun _ : Fin p => 𝟙_ C) (fun _ : Fin q => P)).symm⟩⟩
  · rintro ⟨Y, ⟨pairing⟩, p, q, ⟨e⟩⟩
    let d : Xᘁ ≅ Y := rightDualIso (inferInstance : ExactPairing X Xᘁ) pairing
    exact ⟨p, q, ⟨tensorIso (Iso.refl X) d ≪≫ e ≪≫
      sumBiproductIso (fun _ : Fin p => 𝟙_ C) (fun _ : Fin q => P)⟩⟩

end RMod.BrundanEllis.MathlibBridge
