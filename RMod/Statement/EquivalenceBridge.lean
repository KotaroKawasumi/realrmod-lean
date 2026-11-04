import RMod.Statement.FusionBridge
import RMod.Hierarchy.Instances.EquivalenceComposition

/-! Strong monoidal superequivalences are preserved in both presentations. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.MonoidalCategory
namespace RMod.StatementLegacy.StatementBridge

/-- View the reconstructed even tensor as a morphism in the given even category. -/
def recoveredEvenTensor (C : MonoidalSupercategory) {X X' Y Y' : Even C.super}
    (f : X ⟶ X') (g : Y ⟶ Y') : X ⊗ Y ⟶ X' ⊗ Y' :=
  Legacy.eTensor (toMonoidalData C).monoidal f g

theorem recoveredEvenTensor_eq (C : MonoidalSupercategory) {X X' Y Y' : Even C.super}
    (f : X ⟶ X') (g : Y ⟶ Y') : recoveredEvenTensor C f g = f ⊗ₘ g :=
  toMonoidal_eTensor C f g

/-- The total naturality of the old unit restricts to ordinary even naturality. -/
theorem legacy_unit_natural {C D : Legacy.MonoidalSupercategory}
    (E : Legacy.MonoidalSuperequivalence C D) {X Y : Legacy.Even C.super} (f : X ⟶ Y) :
    f ≫ (E.data.unit Y).hom = (E.data.unit X).hom ≫ E.evenBackward.map (E.evenForward.map f) := by
  apply Legacy.evenPoint_injective
  rw [Legacy.evenPoint_category_comp, Legacy.evenPoint_category_comp]
  change Legacy.tComp _ _ _ = Legacy.tComp _ _ _
  erw [Legacy.evenPoint_functor_map, Legacy.evenPoint_functor_map]
  exact E.laws.unit_natural (Legacy.evenPoint f)

theorem legacy_counit_natural {C D : Legacy.MonoidalSupercategory}
    (E : Legacy.MonoidalSuperequivalence C D) {X Y : Legacy.Even D.super} (f : X ⟶ Y) :
    E.evenForward.map (E.evenBackward.map f) ≫ (E.data.counit Y).hom =
      (E.data.counit X).hom ≫ f := by
  apply Legacy.evenPoint_injective
  rw [Legacy.evenPoint_category_comp, Legacy.evenPoint_category_comp]
  change Legacy.tComp _ _ _ = Legacy.tComp _ _ _
  erw [Legacy.evenPoint_functor_map, Legacy.evenPoint_functor_map]
  exact E.laws.counit_natural (Legacy.evenPoint f)

/-- Rebundle a previous equivalence on the given new source and target. -/
def fromEquivalence {C D : MonoidalSupercategory}
    (E : Legacy.MonoidalSuperequivalence (toMonoidal C) (toMonoidal D)) :
    MonoidalSuperequivalence C D where
  forward := fromFunctor E.forward
  backward := fromFunctor E.backward
  monoidal := {
    εIso := E.data.unitIso
    μIso := E.data.tensorIso
    μIso_hom_natural_left := by
      intro X Y f Z
      let F : Even C.super ⥤ Even D.super := (fromFunctor E.forward).forget
      have h := E.evenCoreMonoidal.μIso_hom_natural_left f Z
      change recoveredEvenTensor D (F.map f) (𝟙 (F.obj Z)) ≫
        (E.data.tensorIso Y Z).hom = (E.data.tensorIso X Z).hom ≫
          F.map (recoveredEvenTensor C f (𝟙 Z)) at h
      rw [recoveredEvenTensor_eq, recoveredEvenTensor_eq, tensorHom_id, tensorHom_id] at h
      exact h
    μIso_hom_natural_right := by
      intro X Y Z f
      let F : Even C.super ⥤ Even D.super := (fromFunctor E.forward).forget
      have h := E.evenCoreMonoidal.μIso_hom_natural_right Z f
      change recoveredEvenTensor D (𝟙 (F.obj Z)) (F.map f) ≫
        (E.data.tensorIso Z Y).hom = (E.data.tensorIso Z X).hom ≫
          F.map (recoveredEvenTensor C (𝟙 Z) f) at h
      rw [recoveredEvenTensor_eq, recoveredEvenTensor_eq, id_tensorHom, id_tensorHom] at h
      exact h
    associativity := by
      intro X Y Z
      let F : Even C.super ⥤ Even D.super := (fromFunctor E.forward).forget
      have h := E.evenCoreMonoidal.associativity X Y Z
      change recoveredEvenTensor D (E.data.tensorIso X Y).hom
        (𝟙 (F.obj Z)) ≫ (E.data.tensorIso (X ⊗ Y) Z).hom ≫ F.map (@MonoidalCategoryStruct.associator (Even C.super) _
          (evenCategoryMonoidal C).toMonoidalCategoryStruct X Y Z).hom =
          (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom ≫
            recoveredEvenTensor D (𝟙 (F.obj X)) (E.data.tensorIso Y Z).hom ≫
              (E.data.tensorIso X (Y ⊗ Z)).hom at h
      rw [recoveredEvenTensor_eq, recoveredEvenTensor_eq, tensorHom_id, id_tensorHom] at h
      exact h
    left_unitality := by
      intro X
      let F : Even C.super ⥤ Even D.super := (fromFunctor E.forward).forget
      have h := E.evenCoreMonoidal.left_unitality X
      change (λ_ (F.obj X)).hom =
        recoveredEvenTensor D E.data.unitIso.hom (𝟙 (F.obj X)) ≫
          (E.data.tensorIso (𝟙_ (Even C.super)) X).hom ≫ F.map (@MonoidalCategoryStruct.leftUnitor (Even C.super) _
          (evenCategoryMonoidal C).toMonoidalCategoryStruct X).hom at h
      rw [recoveredEvenTensor_eq, tensorHom_id] at h
      exact h
    right_unitality := by
      intro X
      let F : Even C.super ⥤ Even D.super := (fromFunctor E.forward).forget
      have h := E.evenCoreMonoidal.right_unitality X
      change (ρ_ (F.obj X)).hom =
        recoveredEvenTensor D (𝟙 (F.obj X)) E.data.unitIso.hom ≫
          (E.data.tensorIso X (𝟙_ (Even C.super))).hom ≫ F.map (@MonoidalCategoryStruct.rightUnitor (Even C.super) _
          (evenCategoryMonoidal C).toMonoidalCategoryStruct X).hom at h
      rw [recoveredEvenTensor_eq, id_tensorHom] at h
      exact h }
  unit := NatIso.ofComponents E.data.unit (fun f => legacy_unit_natural E f)
  counit := NatIso.ofComponents E.data.counit (fun f => legacy_counit_natural E f)
  unit_natural := E.laws.unit_natural
  counit_natural := E.laws.counit_natural
  tensor_natural := E.laws.tensor_natural

/-- Retain every functor and comparison map when extracting the old data. -/
def toEquivalenceData {C D : MonoidalSupercategory} (E : MonoidalSuperequivalence C D) :
    Legacy.MonoidalSuperequivalenceData (toMonoidal C) (toMonoidal D) where
  forward := (toFunctor E.forward).data
  backward := (toFunctor E.backward).data
  tensorIso := E.monoidal.μIso
  unitIso := E.monoidal.εIso
  unit X := E.unit.app X
  counit X := E.counit.app X

theorem toEquivalenceLaws {C D : MonoidalSupercategory} (E : MonoidalSuperequivalence C D) :
    Legacy.MonoidalSuperequivalenceLaws (toEquivalenceData E) where
  forward := (toFunctor E.forward).laws
  backward := (toFunctor E.backward).laws
  unit_natural := E.unit_natural
  counit_natural := E.counit_natural
  tensor_natural := E.tensor_natural
  associativity := by
    intro X Y Z
    let F : Even C.super ⥤ Even D.super := E.forward.forget
    change recoveredEvenTensor D (E.monoidal.μIso X Y).hom
      (𝟙 (F.obj Z)) ≫ (E.monoidal.μIso (X ⊗ Y) Z).hom ≫ F.map (@MonoidalCategoryStruct.associator (Even C.super) _
          (evenCategoryMonoidal C).toMonoidalCategoryStruct X Y Z).hom =
        (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom ≫
          recoveredEvenTensor D (𝟙 (F.obj X)) (E.monoidal.μIso Y Z).hom ≫
            (E.monoidal.μIso X (Y ⊗ Z)).hom
    rw [recoveredEvenTensor_eq, recoveredEvenTensor_eq, tensorHom_id, id_tensorHom]
    exact E.monoidal.associativity X Y Z
  left_unit := by
    intro X
    let F : Even C.super ⥤ Even D.super := E.forward.forget
    change recoveredEvenTensor D E.monoidal.εIso.hom (𝟙 (F.obj X)) ≫
      (E.monoidal.μIso (𝟙_ (Even C.super)) X).hom ≫ F.map (@MonoidalCategoryStruct.leftUnitor (Even C.super) _
          (evenCategoryMonoidal C).toMonoidalCategoryStruct X).hom = (λ_ (F.obj X)).hom
    rw [recoveredEvenTensor_eq, tensorHom_id]
    exact (E.monoidal.left_unitality X).symm
  right_unit := by
    intro X
    let F : Even C.super ⥤ Even D.super := E.forward.forget
    change recoveredEvenTensor D (𝟙 (F.obj X)) E.monoidal.εIso.hom ≫
      (E.monoidal.μIso X (𝟙_ (Even C.super))).hom ≫ F.map (@MonoidalCategoryStruct.rightUnitor (Even C.super) _
          (evenCategoryMonoidal C).toMonoidalCategoryStruct X).hom = (ρ_ (F.obj X)).hom
    rw [recoveredEvenTensor_eq, id_tensorHom]
    exact (E.monoidal.right_unitality X).symm

def toEquivalence {C D : MonoidalSupercategory} (E : MonoidalSuperequivalence C D) :
    Legacy.MonoidalSuperequivalence (toMonoidal C) (toMonoidal D) :=
  ⟨toEquivalenceData E, toEquivalenceLaws E⟩

end RMod.StatementLegacy.StatementBridge
