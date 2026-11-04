import RMod.Classification.Instances.CentralDuality
import RMod.Classification.Proofs.CentralWordRoutes
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic

/-!
# Cancellation of the two central factors in the first duality snake

Both crossings gather into the half-braiding of the square. Centrality
of its inverse contraction moves the whole pair past X, where the two
contraction maps cancel. What remains is the supplied ordinary snake.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification.CentralDuality

open CategoryTheory MonoidalCategory

attribute [local implicit_reducible] CategoryTheory.Center CategoryTheory.Center.tensorObj
  CategoryTheory.Center.tensorUnit

variable {V : Type u} [Category.{v} V] [MonoidalCategory V]

/-- Unit multiplication at the two outer positions leaves the single
middle crossing, tensored with the identity of the outer unit. -/
theorem unit_normalizer (X Y Z P : V) (c : P ⊗ Z ≅ Z ⊗ P) :
    ((tensorIso (α_ (X ⊗ Y) P Z) (Iso.refl (𝟙_ V)) ≪≫
      tensorIso (tensorIso (Iso.refl (X ⊗ Y)) c) (Iso.refl (𝟙_ V)) ≪≫
      tensorIso (α_ (X ⊗ Y) Z P).symm (Iso.refl (𝟙_ V)) ≪≫
      tensorIso (tensorIso (α_ X Y Z) (Iso.refl P)) (Iso.refl (𝟙_ V)) ≪≫
      α_ (X ⊗ (Y ⊗ Z)) P (𝟙_ V) ≪≫ tensorIso (Iso.refl (X ⊗ (Y ⊗ Z))) (ρ_ P)) ≪≫
      (tensorIso (α_ X (Y ⊗ Z) P).symm (Iso.refl (𝟙_ V)) ≪≫
        α_ (X ⊗ (Y ⊗ Z)) P (𝟙_ V) ≪≫ tensorIso (Iso.refl (X ⊗ (Y ⊗ Z))) (ρ_ P)).symm).hom =
    (α_ (X ⊗ Y) P Z ≪≫ tensorIso (Iso.refl (X ⊗ Y)) c ≪≫
      (α_ (X ⊗ Y) Z P).symm ≪≫ tensorIso (α_ X Y Z) (Iso.refl P) ≪≫
        α_ X (Y ⊗ Z) P).hom ⊗ₘ 𝟙 (𝟙_ V) := by
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    tensorIso_hom, tensorIso_inv, Iso.refl_hom, Iso.refl_inv]
  monoidal

theorem positive_snake (X Y : V) (P : Center V) (m : P ⊗ P ≅ 𝟙_ (Center V))
    (η : 𝟙_ V ⟶ X ⊗ Y) (ε : Y ⊗ X ⟶ 𝟙_ V)
    (h : η ▷ X ≫ (α_ X Y X).hom ≫ X ◁ ε = (λ_ X).hom ≫ (ρ_ X).inv) :
    (η ≫ (positive X Y P m).inv) ▷ X ≫ (middle X (Y ⊗ P.1) X P).hom ≫
      X ◁ ((negative X Y P m).hom ≫ ε) = (λ_ X).hom ≫ (ρ_ X).inv := by
  let d : 𝟙_ V ⟶ P.1 ⊗ P.1 := m.inv.f
  let e : P.1 ⊗ P.1 ⟶ 𝟙_ V := m.hom.f
  let b : (P.1 ⊗ P.1) ⊗ X ⟶ X ⊗ (P.1 ⊗ P.1) := ((P ⊗ P).2.β X).hom
  have hc : d ▷ X ≫ b ≫ X ◁ e =
      (λ_ X).hom ≫ (ρ_ X).inv := by
    dsimp only [d, e, b]
    rw [← Category.assoc]
    erw [m.inv.comm]
    change (((λ_ X).hom ≫ (ρ_ X).inv) ≫ X ◁ m.inv.f) ≫ X ◁ m.hom.f = _
    simp only [Category.assoc, ← whiskerLeft_comp, ← Center.comp_f, m.inv_hom_id, Center.id_f]
    change (λ_ X).hom ≫ (ρ_ X).inv ≫ X ◁ 𝟙 (𝟙_ V) = _
    rw [whiskerLeft_id, Category.comp_id]
  calc
    _ = 𝟙 (𝟙_ V ⊗ X) ⊗≫ (η ▷ X) ⊗≫
      (X ⊗ Y) ◁ (d ▷ X ≫ b ≫ X ◁ e) ⊗≫
        (X ◁ ε) ⊗≫ 𝟙 (X ⊗ 𝟙_ V) := by
      simp only [positive, negative, middle, Iso.trans_hom, Iso.trans_inv,
        Iso.symm_hom, Iso.symm_inv, tensorIso_hom, tensorIso_inv,
        Iso.refl_hom, Iso.refl_inv, Functor.mapIso_hom, Functor.mapIso_inv,
        Center.forget_map]
      dsimp only [b]
      rw [CentralWord.tensor_crossing]
      monoidal
    _ = η ▷ X ≫ (α_ X Y X).hom ≫ X ◁ ε := by
      rw [hc]
      monoidal
    _ = _ := h

end RMod.Classification.CentralDuality
