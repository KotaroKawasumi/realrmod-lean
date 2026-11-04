import RMod.Classification.Proofs.InverseMonoidalCoherence

/-!
# Transporting coherence along the constructed comparison

The inverse comparison gives exactly Mathlib's `InducingFunctorData`.
Faithfulness of the inverse equivalence then proves pentagon and triangle
for the already specified target structure, without changing its maps.
-/

set_option autoImplicit false
universe u₁ v₁ u₂ v₂

namespace RMod.Classification

open CategoryTheory CategoryTheory.MonoidalCategory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategoryStruct D]
  (e : C ≌ D) (hD : TensorStructuralLaws D) (d : MonoidalComparison e.functor)

noncomputable def monoidalInducingDataOfComparison : Monoidal.InducingFunctorData e.inverse where
  μIso := (inverseMonoidalComparisonData e hD d.data).tensor
  εIso := (inverseMonoidalComparisonData e hD d.data).unit
  tensorHom_eq := inverseComparison_map_tensor e hD d
  whiskerLeft_eq X {_ _} f := by
    rw [hD.whisker_left, inverseComparison_map_tensor e hD d, Functor.map_id, id_tensorHom]
  whiskerRight_eq {_ _} f Y := by
    rw [hD.whisker_right, inverseComparison_map_tensor e hD d, Functor.map_id, tensorHom_id]
  associator_eq X Y Z := by
    simpa only [Iso.trans_hom, Iso.symm_hom, tensorIso_hom, Iso.refl_hom, Category.assoc] using
      inverseComparison_map_associator e hD d X Y Z
  leftUnitor_eq X := by
    simpa only [Iso.trans_hom, Iso.symm_hom, tensorIso_hom, Iso.refl_hom, Category.assoc] using
      inverseComparison_map_left_unitor e hD d X
  rightUnitor_eq X := by
    simpa only [Iso.trans_hom, Iso.symm_hom, tensorIso_hom, Iso.refl_hom, Category.assoc] using
      inverseComparison_map_right_unitor e hD d X

/-- The target tensor, associator, and unitors are exactly the given formation data. -/
@[implicit_reducible]
noncomputable def monoidalCategoryOfComparison : MonoidalCategory D :=
  Monoidal.induced e.inverse (monoidalInducingDataOfComparison e hD d)

end RMod.Classification
