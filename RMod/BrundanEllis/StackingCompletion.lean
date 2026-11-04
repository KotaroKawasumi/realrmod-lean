import RMod.BrundanEllis.StackingHullFusion

/-! The completed full subcategory and its inclusion satisfy the categorical
part of the stack contract. This general construction is parameterized by
a generating family whose tensor and dual closure must be proved separately. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.MonoidalCategory
namespace RMod.BrundanEllis
variable (C : WeaklyPointedFusionPiSuperCat) {I : Type} (Z : I → Even C)
  [ObjectProperty.IsMonoidal (AddPiHull C Z)]
  (hL : ∀ X : Even (HullCategory C Z), AddPiHull C Z (ᘁX.obj))
  (hR : ∀ X : Even (HullCategory C Z), AddPiHull C Z (X.objᘁ))

def hullFusionInclusion : SuperFunctor (hullFusionCategory C Z hL hR) C :=
  hullInclusion C Z

def hullFusionMonoidal : (hullFusionInclusion C Z hL hR).forget.CoreMonoidal :=
  hullInclusionMonoidal C Z

/-- All degrees are fully faithful, the tensor comparisons respect every
homogeneous map, and the essential image is exactly the specified hull. -/
theorem hullFusion_data :
    let A := hullFusionCategory C Z hL hR
    let F := hullFusionInclusion C Z hL hR
    let M := hullFusionMonoidal C Z hL hR
    (∀ X Y a, Function.Bijective (F.map X Y a)) ∧
    (∀ {X X' Y Y'} (f : THom A X X') (g : THom A Y Y'),
      tComp C
        (tTensor (MonoidalSuperCategory.tensor (C := C))
          MonoidalSuperCategory.tensor_objects (tMap F f) (tMap F g))
        (evenPoint (M.μIso X' Y').hom) =
      tComp C (evenPoint (M.μIso X Y).hom)
        (tMap F (tTensor (MonoidalSuperCategory.tensor (C := A))
          MonoidalSuperCategory.tensor_objects f g))) ∧
    (∀ W : Even C,
      (∃ X : Even A, Nonempty (F.forget.obj X ≅ W)) ↔ AddPiHull C Z W) :=
  ⟨hullInclusion_bijective C Z, hullInclusion_tensor_natural C Z, hullInclusion_image C Z⟩

end RMod.BrundanEllis
