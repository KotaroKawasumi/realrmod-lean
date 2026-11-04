import RMod.Classification.Instances.InverseMonoidalComparison
import RMod.Classification.Proofs.MonoidalComparison
import RMod.Classification.Proofs.TensorBeforeCoherence

/-!
# Coherence of the inverse comparison

All calculations take place after the faithful forward functor. Its
comparison diagrams and the counit then cancel the intermediate tensor
comparisons. Only naturality and bifunctoriality in the target enter.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u₁ v₁ u₂ v₂

namespace RMod.Classification

open CategoryTheory CategoryTheory.MonoidalCategory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategoryStruct C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategoryStruct D]
  (e : C ≌ D) (hD : TensorStructuralLaws D) (d : MonoidalComparison e.functor)

omit [MonoidalCategoryStruct C] [MonoidalCategoryStruct D] in
/-- The composite functor acts by conjugation with its specified counit. -/
theorem equivalence_map_inverse_map {X Y : D} (f : X ⟶ Y) :
    e.functor.map (e.inverse.map f) =
      (e.counitIso.app X).hom ≫ f ≫ (e.counitIso.app Y).inv := by
  apply (cancel_mono (e.counitIso.app Y).hom).1
  dsimp only [Functor.id_obj, Functor.comp_obj]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact e.counit_naturality f

theorem inverseComparison_map_tensor {X X' Y Y' : D} (f : X ⟶ X') (g : Y ⟶ Y') :
    e.inverse.map (f ⊗ₘ g) =
      ((inverseMonoidalComparisonData e hD d.data).tensor X Y).inv ≫
        (e.inverse.map f ⊗ₘ e.inverse.map g) ≫
        ((inverseMonoidalComparisonData e hD d.data).tensor X' Y').hom := by
  apply e.functor.map_injective
  simp only [Functor.map_comp, d.map_tensor, inverseMonoidalComparisonData,
    Functor.preimageIso_hom, Functor.preimageIso_inv, Functor.map_preimage,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, tensorIsoBeforeCoherence,
    equivalence_map_inverse_map, Category.assoc, Iso.hom_inv_id_assoc,
    hD.tensor_comp_reverse_assoc,
    Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

end RMod.Classification
