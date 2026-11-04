import RMod.Classification.Instances.TensorIsoBeforeCoherence

/-!
# Conjugation formulas for a monoidal comparison

These are consequences of the specified functor diagrams and inverse
identities. In particular, no pentagon or triangle in the target is used.
-/

set_option autoImplicit false
universe u₁ v₁ u₂ v₂

namespace RMod.Classification.MonoidalComparison

open CategoryTheory CategoryTheory.MonoidalCategory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategoryStruct C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategoryStruct D]
  {F : C ⥤ D} (d : MonoidalComparison F) (hD : TensorStructuralLaws D)

theorem map_tensor {X X' Y Y' : C} (f : X ⟶ X') (g : Y ⟶ Y') :
    F.map (f ⊗ₘ g) = (d.data.tensor X Y).inv ≫
      (F.map f ⊗ₘ F.map g) ≫ (d.data.tensor X' Y').hom := by
  rw [d.laws.naturality, Iso.inv_hom_id_assoc]

include hD

theorem map_associator (X Y Z : C) :
    F.map (α_ X Y Z).hom =
      (d.data.tensor (X ⊗ Y) Z).inv ≫
        ((d.data.tensor X Y).inv ⊗ₘ (𝟙 (F.obj Z))) ≫
        (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom ≫
        ((𝟙 (F.obj X)) ⊗ₘ (d.data.tensor Y Z).hom) ≫
        (d.data.tensor X (Y ⊗ Z)).hom := by
  let T := tensorIsoBeforeCoherence hD (d.data.tensor X Y) (Iso.refl (F.obj Z))
  have he := congrArg (fun f => (d.data.tensor (X ⊗ Y) Z).inv ≫ T.inv ≫ f)
    (d.laws.associativity X Y Z)
  change (d.data.tensor (X ⊗ Y) Z).inv ≫ T.inv ≫
      (T.hom ≫ (d.data.tensor (X ⊗ Y) Z).hom ≫ F.map (α_ X Y Z).hom) = _ at he
  simp only [Iso.inv_hom_id_assoc] at he
  simpa only [T, tensorIsoBeforeCoherence, Iso.refl_inv] using he

theorem map_left_unitor (X : C) :
    F.map (λ_ X).hom = (d.data.tensor (𝟙_ C) X).inv ≫
      (d.data.unit.inv ⊗ₘ (𝟙 (F.obj X))) ≫ (λ_ (F.obj X)).hom := by
  let T := tensorIsoBeforeCoherence hD d.data.unit (Iso.refl (F.obj X))
  have he := congrArg (fun f => (d.data.tensor (𝟙_ C) X).inv ≫ T.inv ≫ f)
    (d.laws.left_unit X)
  change (d.data.tensor (𝟙_ C) X).inv ≫ T.inv ≫
      (T.hom ≫ (d.data.tensor (𝟙_ C) X).hom ≫ F.map (λ_ X).hom) = _ at he
  simp only [Iso.inv_hom_id_assoc] at he
  simpa only [T, tensorIsoBeforeCoherence, Iso.refl_inv] using he

theorem map_right_unitor (X : C) :
    F.map (ρ_ X).hom = (d.data.tensor X (𝟙_ C)).inv ≫
      ((𝟙 (F.obj X)) ⊗ₘ d.data.unit.inv) ≫ (ρ_ (F.obj X)).hom := by
  let T := tensorIsoBeforeCoherence hD (Iso.refl (F.obj X)) d.data.unit
  have he := congrArg (fun f => (d.data.tensor X (𝟙_ C)).inv ≫ T.inv ≫ f)
    (d.laws.right_unit X)
  change (d.data.tensor X (𝟙_ C)).inv ≫ T.inv ≫
      (T.hom ≫ (d.data.tensor X (𝟙_ C)).hom ≫ F.map (ρ_ X).hom) = _ at he
  simp only [Iso.inv_hom_id_assoc] at he
  simpa only [T, tensorIsoBeforeCoherence, Iso.refl_inv] using he

end RMod.Classification.MonoidalComparison
