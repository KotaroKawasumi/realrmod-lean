import RMod.BrundanEllis.StackingHullSums
import Mathlib.CategoryTheory.Enriched.Ordinary.Basic

/-! The actual full enriched subcategory of the prescribed completion.
Objects are precisely the even retracts of finite sums of generators and their
parity shifts. Its inclusion keeps every homogeneous Hom space unchanged. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace RMod.BrundanEllis

variable (C : WeaklyPointedFusionPiSuperCat) {I : Type} (Z : I → Even C)

/-- This carrier adds no chosen splitting or presentation to an object. -/
def HullCategory := ObjectProperty.FullSubcategory (AddPiHull C Z)

instance hullEnriched : SuperCategory (HullCategory C Z) :=
  inferInstanceAs (SuperCategory (ObjectProperty.FullSubcategory (AddPiHull C Z)))

/-- The superfunctor includes exactly the homogeneous Hom spaces of the ambient category. -/
def hullInclusion : SuperFunctor (HullCategory C Z) C where
  obj X := X.obj
  map _ _ := 𝟙 _
  map_id _ := by simp; rfl
  map_comp _ _ _ := by simp; rfl

theorem hullInclusion_bijective (X Y : HullCategory C Z) (a : ZMod 2) :
    Function.Bijective ((hullInclusion C Z).map X Y a) := Function.bijective_id

/-- The categorical essential image is exactly the completion predicate. -/
theorem hullInclusion_image (X : Even C) :
    (∃ Y : Even (HullCategory C Z), Nonempty ((hullInclusion C Z).forget.obj Y ≅ X)) ↔
      AddPiHull C Z X := by
  constructor
  · rintro ⟨Y, ⟨e⟩⟩
    exact (AddPiHull.iso_iff e).mp Y.property
  · intro h
    exact ⟨evenObj _ ⟨X, h⟩, ⟨Iso.refl _⟩⟩

/-- Both original and shifted generators occur as actual objects of the full subcategory. -/
def hullGenerator (i : I) : HullCategory C Z := ⟨Z i, AddPiHull.generator i⟩
def hullParityGenerator (i : I) : HullCategory C Z :=
  ⟨evenObj C (MonoidalPiSuperCategory.pi (C := C)) ⊗ Z i, AddPiHull.parityGenerator i⟩

end RMod.BrundanEllis
