import RMod.BrundanEllis.StackingProductWhisker
import RMod.BrundanEllis.StackingTensorNaturality
import RMod.BrundanEllis.MonoidalBridge

/-! All-degree naturality of the component associator and unitors in the
super tensor product. The only inputs are the given component structures. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
namespace RMod.BrundanEllis.Stacking
variable {A B : Type} [SuperCategory A] [SuperCategory B]
  [MonoidalCategory (Even A)] [MonoidalCategory (Even B)]
  [MonoidalSuperCategory A] [MonoidalSuperCategory B]
local instance : RMod.MonoidalEnrichedCategory SuperVec A := Bridge.toEnriched A
local instance : RMod.MonoidalEnrichedCategory SuperVec B := Bridge.toEnriched B

/-- The established bridge adds only an identity source transport. -/
theorem componentTensorMap (C : Type) [SuperCategory C]
    [MonoidalCategory (Even C)] [MonoidalSuperCategory C]
    (X X' Y Y' : Even C) :
    RMod.enrichedTensorMap SuperVec (Bridge.toEnriched C).tensor
      (Bridge.toEnriched C).tensor_objects X X' Y Y' =
    enrichedTensorMap (C := C) MonoidalSuperCategory.tensor
      MonoidalSuperCategory.tensor_objects X X' Y Y' := by
  simp only [RMod.enrichedTensorMap, eqToHom_refl, Category.id_comp]
  rfl

/-- Typed projections retain the even categories during Hom calculations. -/
def productFirst (X : Even (SuperTensorProduct A B)) : Even A :=
  evenObj A (ForgetEnrichment.to SuperVec X).1
def productSecond (X : Even (SuperTensorProduct A B)) : Even B :=
  evenObj B (ForgetEnrichment.to SuperVec X).2

@[simp] theorem productFirst_tensor (X Y : Even (SuperTensorProduct A B)) :
    productFirst (X ⊗ Y) = productFirst X ⊗ productFirst Y := rfl
@[simp] theorem productSecond_tensor (X Y : Even (SuperTensorProduct A B)) :
    productSecond (X ⊗ Y) = productSecond X ⊗ productSecond Y := rfl
@[simp] theorem productFirst_unit : productFirst (𝟙_ (Even (SuperTensorProduct A B))) =
    (𝟙_ (Even A)) := rfl
@[simp] theorem productSecond_unit : productSecond (𝟙_ (Even (SuperTensorProduct A B))) =
    (𝟙_ (Even B)) := rfl

@[simp] theorem product_associator_hom (X Y Z : Even (SuperTensorProduct A B)) :
    (α_ X Y Z).hom = (productPair A B).map
      (X := ((productFirst X ⊗ productFirst Y) ⊗ productFirst Z,
        (productSecond X ⊗ productSecond Y) ⊗ productSecond Z))
      (Y := (productFirst X ⊗ (productFirst Y ⊗ productFirst Z),
        productSecond X ⊗ (productSecond Y ⊗ productSecond Z)))
      ((α_ (productFirst X) (productFirst Y) (productFirst Z)).hom,
       (α_ (productSecond X) (productSecond Y) (productSecond Z)).hom) := rfl
@[simp] theorem product_leftUnitor_hom (X : Even (SuperTensorProduct A B)) :
    (λ_ X).hom = (productPair A B).map
      (X := ((𝟙_ (Even A)) ⊗ productFirst X, (𝟙_ (Even B)) ⊗ productSecond X))
      (Y := (productFirst X, productSecond X))
      ((λ_ (productFirst X)).hom, (λ_ (productSecond X)).hom) := rfl
@[simp] theorem product_rightUnitor_hom (X : Even (SuperTensorProduct A B)) :
    (ρ_ X).hom = (productPair A B).map
      (X := (productFirst X ⊗ (𝟙_ (Even A)), productSecond X ⊗ (𝟙_ (Even B))))
      (Y := (productFirst X, productSecond X))
      ((ρ_ (productFirst X)).hom, (ρ_ (productSecond X)).hom) := rfl

@[simp] theorem product_whisker_left_typed (X : Even (SuperTensorProduct A B))
    {Y Z : Even A × Even B} (f : Y ⟶ Z) :
    eHomWhiskerLeft SuperVec X ((productPair A B).map f) =
      eHomWhiskerLeft SuperVec (productFirst X) f.1 ⊗ₘ
        eHomWhiskerLeft SuperVec (productSecond X) f.2 :=
  product_whisker_left (productFirst X, productSecond X) f
@[simp] theorem product_whisker_right_typed {X Y : Even A × Even B}
    (f : X ⟶ Y) (Z : Even (SuperTensorProduct A B)) :
    eHomWhiskerRight SuperVec ((productPair A B).map f) Z =
      eHomWhiskerRight SuperVec f.1 (productFirst Z) ⊗ₘ
        eHomWhiskerRight SuperVec f.2 (productSecond Z) :=
  product_whisker_right f (productFirst Z, productSecond Z)

abbrev productTensorMap (X X' Y Y' : Even (SuperTensorProduct A B)) :=
  (productTensor A B).map
    (ForgetEnrichment.to SuperVec X, ForgetEnrichment.to SuperVec Y)
    (ForgetEnrichment.to SuperVec X', ForgetEnrichment.to SuperVec Y')

theorem productTensorMap_data (X X' Y Y' : Even (SuperTensorProduct A B)) :
    productTensorMap X X' Y Y' =
    tensorμ
      (SHom A (ForgetEnrichment.to SuperVec (productFirst X))
        (ForgetEnrichment.to SuperVec (productFirst X')))
      (SHom B (ForgetEnrichment.to SuperVec (productSecond X))
        (ForgetEnrichment.to SuperVec (productSecond X')))
      (SHom A (ForgetEnrichment.to SuperVec (productFirst Y))
        (ForgetEnrichment.to SuperVec (productFirst Y')))
      (SHom B (ForgetEnrichment.to SuperVec (productSecond Y))
        (ForgetEnrichment.to SuperVec (productSecond Y'))) ≫
      (enrichedTensorMap (C := A) MonoidalSuperCategory.tensor MonoidalSuperCategory.tensor_objects
        (productFirst X) (productFirst X') (productFirst Y) (productFirst Y') ⊗ₘ
       enrichedTensorMap (C := B) MonoidalSuperCategory.tensor MonoidalSuperCategory.tensor_objects
        (productSecond X) (productSecond X') (productSecond Y) (productSecond Y')) :=
  productTensor_map A B _ _

theorem product_associator_naturality
    (X X' Y Y' Z Z' : Even (SuperTensorProduct A B)) :
    (productTensorMap X X' Y Y' ⊗ₘ 𝟙 (SHom (SuperTensorProduct A B)
      (ForgetEnrichment.to SuperVec Z) (ForgetEnrichment.to SuperVec Z'))) ≫
      productTensorMap (X ⊗ Y) (X' ⊗ Y') Z Z' ≫
      eHomWhiskerLeft SuperVec ((X ⊗ Y) ⊗ Z) (α_ X' Y' Z').hom =
    (α_ (SHom (SuperTensorProduct A B) (ForgetEnrichment.to SuperVec X) (ForgetEnrichment.to SuperVec X'))
      (SHom (SuperTensorProduct A B) (ForgetEnrichment.to SuperVec Y) (ForgetEnrichment.to SuperVec Y'))
      (SHom (SuperTensorProduct A B) (ForgetEnrichment.to SuperVec Z) (ForgetEnrichment.to SuperVec Z'))).hom ≫
      (𝟙 (SHom (SuperTensorProduct A B) (ForgetEnrichment.to SuperVec X)
        (ForgetEnrichment.to SuperVec X')) ⊗ₘ productTensorMap Y Y' Z Z') ≫
      productTensorMap X X' (Y ⊗ Z) (Y' ⊗ Z') ≫
      eHomWhiskerRight SuperVec (α_ X Y Z).hom (X' ⊗ (Y' ⊗ Z')) := by
  simp only [product_associator_hom, product_whisker_left_typed, product_whisker_right_typed,
    productTensorMap_data, productFirst_tensor, productSecond_tensor,
    tensorHom_id, id_tensorHom]
  apply tensor_assoc_naturality
  · simpa only [componentTensorMap, tensorHom_id, id_tensorHom, productFirst, productSecond, evenObj, SHom, ForgetEnrichment.to, ForgetEnrichment.of] using
      RMod.MonoidalEnrichedCategory.associator_naturality (C := A) SuperVec
        (productFirst X) (productFirst X') (productFirst Y) (productFirst Y')
        (productFirst Z) (productFirst Z')
  · simpa only [componentTensorMap, tensorHom_id, id_tensorHom, productFirst, productSecond, evenObj, SHom, ForgetEnrichment.to, ForgetEnrichment.of] using
      RMod.MonoidalEnrichedCategory.associator_naturality (C := B) SuperVec
        (productSecond X) (productSecond X') (productSecond Y) (productSecond Y')
        (productSecond Z) (productSecond Z')

theorem product_unit_id :
    eId (C := SuperTensorProduct A B) SuperVec
      (ForgetEnrichment.to SuperVec (𝟙_ (Even (SuperTensorProduct A B)))) =
    (λ_ (𝟙_ SuperVec)).inv ≫
      (eId (C := A) SuperVec (ForgetEnrichment.to SuperVec (𝟙_ (Even A))) ⊗ₘ
       eId (C := B) SuperVec (ForgetEnrichment.to SuperVec (𝟙_ (Even B)))) := rfl

theorem product_left_naturality (X Y : Even (SuperTensorProduct A B)) :
    (λ_ (SHom (SuperTensorProduct A B) (ForgetEnrichment.to SuperVec X) (ForgetEnrichment.to SuperVec Y))).inv ≫ (eId (C := SuperTensorProduct A B) SuperVec
        (ForgetEnrichment.to SuperVec (𝟙_ (Even (SuperTensorProduct A B)))) ⊗ₘ 𝟙 (SHom (SuperTensorProduct A B) (ForgetEnrichment.to SuperVec X) (ForgetEnrichment.to SuperVec Y))) ≫
      productTensorMap (𝟙_ _) (𝟙_ _) X Y ≫
      eHomWhiskerLeft SuperVec ((𝟙_ _) ⊗ X) (λ_ Y).hom =
    eHomWhiskerRight SuperVec (λ_ X).hom Y := by
  simp only [product_leftUnitor_hom, product_whisker_left_typed, product_whisker_right_typed,
    productTensorMap_data, product_unit_id, productFirst_tensor, productSecond_tensor,
    productFirst_unit, productSecond_unit, tensorHom_id]
  apply tensor_left_naturality
  · simpa only [componentTensorMap, tensorHom_id, productFirst, productSecond, evenObj, SHom, ForgetEnrichment.to, ForgetEnrichment.of] using
      RMod.MonoidalEnrichedCategory.left_naturality (C := A) SuperVec (productFirst X) (productFirst Y)
  · simpa only [componentTensorMap, tensorHom_id, productFirst, productSecond, evenObj, SHom, ForgetEnrichment.to, ForgetEnrichment.of] using
      RMod.MonoidalEnrichedCategory.left_naturality (C := B) SuperVec (productSecond X) (productSecond Y)

theorem product_right_naturality (X Y : Even (SuperTensorProduct A B)) :
    (ρ_ (SHom (SuperTensorProduct A B) (ForgetEnrichment.to SuperVec X) (ForgetEnrichment.to SuperVec Y))).inv ≫ (𝟙 (SHom (SuperTensorProduct A B) (ForgetEnrichment.to SuperVec X) (ForgetEnrichment.to SuperVec Y)) ⊗ₘ eId (C := SuperTensorProduct A B) SuperVec
        (ForgetEnrichment.to SuperVec (𝟙_ (Even (SuperTensorProduct A B))))) ≫
      productTensorMap X Y (𝟙_ _) (𝟙_ _) ≫
      eHomWhiskerLeft SuperVec (X ⊗ (𝟙_ _)) (ρ_ Y).hom =
    eHomWhiskerRight SuperVec (ρ_ X).hom Y := by
  simp only [product_rightUnitor_hom, product_whisker_left_typed, product_whisker_right_typed,
    productTensorMap_data, product_unit_id, productFirst_tensor, productSecond_tensor,
    productFirst_unit, productSecond_unit, id_tensorHom]
  apply tensor_right_naturality
  · simpa only [componentTensorMap, id_tensorHom, productFirst, productSecond, evenObj, SHom, ForgetEnrichment.to, ForgetEnrichment.of] using
      RMod.MonoidalEnrichedCategory.right_naturality (C := A) SuperVec (productFirst X) (productFirst Y)
  · simpa only [componentTensorMap, id_tensorHom, productFirst, productSecond, evenObj, SHom, ForgetEnrichment.to, ForgetEnrichment.of] using
      RMod.MonoidalEnrichedCategory.right_naturality (C := B) SuperVec (productSecond X) (productSecond Y)

end RMod.BrundanEllis.Stacking
