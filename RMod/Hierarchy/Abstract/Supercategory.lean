import RMod.Hierarchy.Instances.SuperVecLinear
import Mathlib.CategoryTheory.Enriched.Basic

/-! Operations and laws for real sVec-enriched categories. -/

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped BigOperators TensorProduct
namespace RMod.Legacy

structure SupercategoryData where
  Obj : Type
  Hom : Obj → Obj → SuperVec
  id : ∀ X, 𝟙_ SuperVec ⟶ Hom X X
  comp : ∀ X Y Z, Hom X Y ⊗ Hom Y Z ⟶ Hom X Z

structure SupercategoryLaws (d : SupercategoryData) : Prop where
  id_comp : ∀ X Y, (λ_ _).inv ≫ d.id X ▷ _ ≫ d.comp X X Y = 𝟙 _
  comp_id : ∀ X Y, (ρ_ _).inv ≫ _ ◁ d.id Y ≫ d.comp X Y Y = 𝟙 _
  assoc : ∀ W X Y Z,
    (α_ _ _ _).inv ≫ d.comp W X Y ▷ _ ≫ d.comp W Y Z =
      _ ◁ d.comp X Y Z ≫ d.comp W X Z

structure Supercategory where
  data : SupercategoryData
  laws : SupercategoryLaws data

instance (C : Supercategory) : EnrichedCategory SuperVec C.data.Obj where
  Hom := C.data.Hom
  id := C.data.id
  comp := C.data.comp
  id_comp := C.laws.id_comp
  comp_id := C.laws.comp_id
  assoc := C.laws.assoc

abbrev Even (C : Supercategory) := ForgetEnrichment SuperVec C.data.Obj
def evenObj (C : Supercategory) (X : C.data.Obj) : Even C :=
  ForgetEnrichment.of SuperVec X
abbrev EHom (d : SupercategoryData) (X Y : d.Obj) :=
  𝟙_ SuperVec ⟶ d.Hom X Y
def eComp (d : SupercategoryData) {X Y Z : d.Obj}
    (f : EHom d X Y) (g : EHom d Y Z) : EHom d X Z :=
  (λ_ (𝟙_ SuperVec)).inv ≫ (f ⊗ₘ g) ≫ d.comp X Y Z

/-! Total Hom spaces combine both graded components of the specified enrichment. -/
abbrev THom (d : SupercategoryData) (X Y : d.Obj) :=
  (a : ZMod 2) → d.Hom X Y a
def homogeneousPoint {V : SuperVec} (a : ZMod 2)
    (f : (GradedObject.single a).obj (ModuleCat.of ℝ ℝ) ⟶ V) : (b : ZMod 2) → V b :=
  fun b => if h : b = a then
    f b ((GradedObject.singleObjApplyIsoOfEq a (ModuleCat.of ℝ ℝ) b h).inv 1) else 0
def evenPoint {V : SuperVec} (f : 𝟙_ SuperVec ⟶ V) := homogeneousPoint 0 f

end RMod.Legacy
