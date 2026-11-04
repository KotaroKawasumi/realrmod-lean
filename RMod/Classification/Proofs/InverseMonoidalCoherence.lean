import RMod.Classification.Proofs.InverseMonoidalComparison

/-!
# The inverse comparison preserves associators and unitors

After applying the faithful forward functor, the two sides reduce to the
same counit conjugate of the given target structure map. Its naturality
is the final step. Target pentagon and triangle are not hypotheses.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u₁ v₁ u₂ v₂

namespace RMod.Classification

open CategoryTheory CategoryTheory.MonoidalCategory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategoryStruct C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategoryStruct D]
  (e : C ≌ D) (hD : TensorStructuralLaws D) (d : MonoidalComparison e.functor)

theorem inverseComparison_map_associator (X Y Z : D) :
    let M := inverseMonoidalComparisonData e hD d.data
    e.inverse.map (α_ X Y Z).hom =
      (M.tensor (X ⊗ Y) Z).inv ≫ ((M.tensor X Y).inv ⊗ₘ (𝟙 (e.inverse.obj Z))) ≫
        (α_ (e.inverse.obj X) (e.inverse.obj Y) (e.inverse.obj Z)).hom ≫
        ((𝟙 (e.inverse.obj X)) ⊗ₘ (M.tensor Y Z).hom) ≫ (M.tensor X (Y ⊗ Z)).hom := by
  dsimp only
  apply e.functor.map_injective
  simp only [Functor.map_comp, d.map_tensor, d.map_associator hD, Functor.map_id,
    inverseMonoidalComparisonData, Functor.preimageIso_hom, Functor.preimageIso_inv,
    Functor.map_preimage, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    tensorIsoBeforeCoherence, equivalence_map_inverse_map]
  dsimp only [Functor.id_obj, Functor.comp_obj]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc,
    hD.tensor_comp_reverse_assoc, Iso.hom_inv_id, Iso.inv_hom_id,
    Category.id_comp, Category.comp_id]
  have hn := congrArg (fun f =>
    (e.counitIso.app ((X ⊗ Y) ⊗ Z)).hom ≫ f ≫
      ((e.counitIso.app X).hom ⊗ₘ ((e.counitIso.app Y).hom ⊗ₘ (e.counitIso.app Z).hom)) ≫
      (e.counitIso.app (X ⊗ (Y ⊗ Z))).inv)
    (hD.associator_naturality (e.counitIso.app X).inv
      (e.counitIso.app Y).inv (e.counitIso.app Z).inv)
  simp only [Functor.id_obj, Category.assoc, hD.tensor_comp_reverse_assoc, hD.tensor_comp_reverse,
    Iso.inv_hom_id, hD.tensor_id, Category.id_comp] at hn
  exact hn.symm

theorem inverseComparison_map_left_unitor (X : D) :
    let M := inverseMonoidalComparisonData e hD d.data
    e.inverse.map (λ_ X).hom = (M.tensor (𝟙_ D) X).inv ≫
      (M.unit.inv ⊗ₘ (𝟙 (e.inverse.obj X))) ≫ (λ_ (e.inverse.obj X)).hom := by
  dsimp only
  apply e.functor.map_injective
  simp only [Functor.map_comp, d.map_tensor, d.map_left_unitor hD, Functor.map_id,
    inverseMonoidalComparisonData, Functor.preimageIso_inv,
    Functor.map_preimage, Iso.trans_inv, Iso.symm_inv,
    tensorIsoBeforeCoherence, equivalence_map_inverse_map]
  dsimp only [Functor.id_obj, Functor.comp_obj]
  simp only [Category.assoc, Iso.hom_inv_id_assoc,
    hD.tensor_comp_reverse_assoc, Iso.hom_inv_id, Iso.inv_hom_id,
    Category.comp_id]
  rw [hD.left_unitor_naturality]

theorem inverseComparison_map_right_unitor (X : D) :
    let M := inverseMonoidalComparisonData e hD d.data
    e.inverse.map (ρ_ X).hom = (M.tensor X (𝟙_ D)).inv ≫
      ((𝟙 (e.inverse.obj X)) ⊗ₘ M.unit.inv) ≫ (ρ_ (e.inverse.obj X)).hom := by
  dsimp only
  apply e.functor.map_injective
  simp only [Functor.map_comp, d.map_tensor, d.map_right_unitor hD, Functor.map_id,
    inverseMonoidalComparisonData, Functor.preimageIso_inv,
    Functor.map_preimage, Iso.trans_inv, Iso.symm_inv,
    tensorIsoBeforeCoherence, equivalence_map_inverse_map]
  dsimp only [Functor.id_obj, Functor.comp_obj]
  simp only [Category.assoc, Iso.hom_inv_id_assoc,
    hD.tensor_comp_reverse_assoc, Iso.hom_inv_id, Iso.inv_hom_id,
    Category.comp_id]
  rw [hD.right_unitor_naturality]

end RMod.Classification
