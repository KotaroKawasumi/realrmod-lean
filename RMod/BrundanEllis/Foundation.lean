import RMod.Enriched.SuperSurface

/-!
Canonical Mathlib structures supporting the Brundan--Ellis declaration surface.
The implementation reuses the established enrichment and total-composition laws.
This module does not import Challenge; each data contract uses ordinary equality.
See docs/BRUNDAN_ELLIS_INTERFACE.md for the paper/Lean composition convention.
-/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped BigOperators TensorProduct
universe u u₁ u₂
-- Keep the graded tensor's colimit witnesses canonical, as in Mathlib-only Challenge.
attribute [-instance] RMod.Legacy.moduleCatHasInitial
namespace RMod.BrundanEllis

/-! Real super vector spaces with the graded tensor product and Koszul symmetry. -/
@[implicit_reducible] def SuperVec := GradedObject (ZMod 2) (ModuleCat.{0} ℝ)
instance : Category SuperVec := GradedObject.categoryOfGradedObjects (ZMod 2)
instance : MonoidalCategory SuperVec := GradedObject.monoidalCategory
def koszulMap (X Y : SuperVec) (a : ZMod 2) : (X ⊗ Y) a ⟶ (Y ⊗ X) a :=
  GradedObject.Monoidal.tensorObjDesc fun i j hij =>
    ((-1 : ℝ) ^ (i * j).val) •
      ((β_ (X i) (Y j)).hom ≫
        GradedObject.Monoidal.ιTensorObj Y X j i a ((add_comm j i).trans hij))

instance superVecSymmetric : SymmetricCategory SuperVec := RMod.superVecSymmetric

/-- Both directions of the chosen symmetry are the specified Koszul maps. -/
theorem superVecSymmetric_data (X Y : SuperVec) :
    let S := superVecSymmetric
    (S.braiding X Y).hom = koszulMap X Y ∧
      (S.braiding X Y).inv = koszulMap Y X := ⟨rfl, rfl⟩

abbrev oddLine : SuperVec :=
  (GradedObject.single (1 : ZMod 2)).obj (ModuleCat.of ℝ ℝ)

/-! Supercategories are structures on carriers; the even category is a separate type synonym. -/
abbrev SuperCategory (C : Type u) := EnrichedCategory SuperVec C
abbrev SuperFunctor (C : Type u₁) (D : Type u₂) [SuperCategory C] [SuperCategory D] :=
  EnrichedFunctor SuperVec C D
abbrev SHom (C : Type u) [SuperCategory C] (X Y : C) : SuperVec := X ⟶[SuperVec] Y
abbrev Even (C : Type u) [SuperCategory C] := ForgetEnrichment SuperVec C
def evenObj (C : Type u) [SuperCategory C] (X : C) : Even C := ForgetEnrichment.of SuperVec X

/-! Total Hom spaces combine both graded components of the specified enrichment. -/
abbrev THom (d : Type u) [SuperCategory d] (X Y : d) :=
  (a : ZMod 2) → SHom d X Y a
def homogeneousPoint {V : SuperVec} (a : ZMod 2)
    (f : (GradedObject.single a).obj (ModuleCat.of ℝ ℝ) ⟶ V) (b : ZMod 2) : V b :=
  if h : b = a then
    f b ((GradedObject.singleObjApplyIsoOfEq a (ModuleCat.of ℝ ℝ) b h).inv 1) else 0
def evenPoint {V : SuperVec} (f : 𝟙_ SuperVec ⟶ V) := homogeneousPoint 0 f
def tComp (d : Type u) [SuperCategory d] {X Y Z : d}
    (f : THom d X Y) (g : THom d Y Z) (a : ZMod 2) : SHom d X Z a :=
  ∑ i : ZMod 2, eComp SuperVec (X : d) Y Z a
    (GradedObject.Monoidal.ιTensorObj (SHom d X Y) (SHom d Y Z)
      i (a - i) a ((add_comm i (a - i)).trans (sub_add_cancel a i)) (f i ⊗ₜ[ℝ] g (a - i)))

@[implicit_reducible] def TotalCategory (C : Type u) [SuperCategory C] : Type u := C
def totalObj (C : Type u) [SuperCategory C] (X : C) : TotalCategory C := X
instance totalCategoryCategory (C : Type u) [SuperCategory C] : Category.{0} (TotalCategory C) where
  Hom := THom C
  id X := evenPoint (eId (C := C) SuperVec (X : C))
  comp := tComp C
  id_comp := fun {_ _} f => RMod.EnrichedSupport.tComp_id_left C f
  comp_id := fun {_ _} f => RMod.EnrichedSupport.tComp_id_right C f
  assoc := fun {_ _ _ _} f g h => RMod.EnrichedSupport.tComp_assoc C f g h

/-- The total category uses exactly the Hom spaces, identities, and convolution above. -/
theorem totalCategoryCategory_data (C : Type u) [SuperCategory C] :
    (totalCategoryCategory C).toCategoryStruct =
      { Hom := THom C
        id X := evenPoint (eId (C := C) SuperVec (X : C))
        comp := tComp C } := rfl

instance totalCategoryPreadditive (C : Type u) [SuperCategory C] : Preadditive (TotalCategory C) where
  homGroup X Y := Pi.addCommGroup
  add_comp := fun _ _ _ f g h => RMod.EnrichedSupport.tComp_add_left C f g h
  comp_add := fun _ _ _ f g h => RMod.EnrichedSupport.tComp_add_right C f g h

/-- Addition on total morphisms is the pointwise Mathlib additive group structure. -/
theorem totalCategoryPreadditive_data (C : Type u) [SuperCategory C] (X Y : TotalCategory C) :
    (totalCategoryPreadditive C).homGroup X Y =
      (Pi.addCommGroup : AddCommGroup (THom C X Y)) := rfl

instance totalCategoryLinear (C : Type u) [SuperCategory C] : Linear ℝ (TotalCategory C) where
  homModule X Y := Pi.module (ZMod 2) (fun a => SHom C X Y a) ℝ
  smul_comp := fun _ _ _ r f g => RMod.EnrichedSupport.tComp_smul_left C r f g
  comp_smul := fun _ _ _ f r g => RMod.EnrichedSupport.tComp_smul_right C r f g

/-- Scalar multiplication on total morphisms is the pointwise Mathlib module structure. -/
theorem totalCategoryLinear_data (C : Type u) [SuperCategory C] (X Y : TotalCategory C) :
    (totalCategoryLinear C).homModule X Y =
      (Pi.module (ZMod 2) (fun a => SHom C X Y a) ℝ) := rfl

instance evenCategoryPreadditive (C : Type u) [SuperCategory C] : Preadditive (Even C) where
  homGroup X Y := Pi.addCommGroup
  add_comp := (RMod.evenCategoryPreadditive C).add_comp
  comp_add := (RMod.evenCategoryPreadditive C).comp_add

/-- Addition on even morphisms is inherited from the specified sVec Hom objects. -/
theorem evenCategoryPreadditive_data (C : Type u) [SuperCategory C] (X Y : Even C) :
    (evenCategoryPreadditive C).homGroup X Y =
      Pi.addCommGroup := rfl

def grade (C : Type u) [SuperCategory C] (X Y : TotalCategory C) (a : ZMod 2) :
    Submodule ℝ (X ⟶ Y) := Submodule.pi {a}ᶜ (fun _ => ⊥)
/-- The grading is exactly support in the specified homogeneous component. -/
theorem grade_data (C : Type u) [SuperCategory C] (X Y : TotalCategory C) (a : ZMod 2) :
    grade C X Y a = (Submodule.pi {a}ᶜ (fun _ => ⊥) : Submodule ℝ (THom C X Y)) := rfl

abbrev SameParityOrbit (C : Type u) [SuperCategory C] (X Y : TotalCategory C) : Prop :=
  ∃ (a : ZMod 2) (e : X ≅ Y), e.hom ∈ grade C X Y a ∧ e.inv ∈ grade C Y X a

/-! The product enrichment uses Mathlib's chronological order of composition.
Its Hom family is fixed before identities, composition and laws are supplied. -/
def SuperTensorProduct (C : Type u₁) (D : Type u₂) := C × D
instance superTensorProductEnriched (C : Type u₁) (D : Type u₂)
    [SuperCategory C] [SuperCategory D] : SuperCategory (SuperTensorProduct C D) where
  Hom X Y := SHom C X.1 Y.1 ⊗ SHom D X.2 Y.2
  id := (RMod.EnrichedSupport.productEnrichment SuperVec C D).id
  comp := (RMod.EnrichedSupport.productEnrichment SuperVec C D).comp
  id_comp := (RMod.EnrichedSupport.productEnrichment SuperVec C D).id_comp
  comp_id := (RMod.EnrichedSupport.productEnrichment SuperVec C D).comp_id
  assoc := (RMod.EnrichedSupport.productEnrichment SuperVec C D).assoc

theorem superTensorProductEnriched_data (C : Type u₁) (D : Type u₂)
    [SuperCategory C] [SuperCategory D] :
    let E := superTensorProductEnriched C D
    (∀ X Y, E.Hom X Y = SHom C X.1 Y.1 ⊗ SHom D X.2 Y.2) ∧
    (∀ X, E.id X = (λ_ (𝟙_ SuperVec)).inv ≫ (eId SuperVec X.1 ⊗ₘ eId SuperVec X.2)) ∧
    (∀ X Y Z, E.comp X Y Z = tensorμ _ _ _ _ ≫
      (eComp SuperVec X.1 Y.1 Z.1 ⊗ₘ eComp SuperVec X.2 Y.2 Z.2)) :=
  ⟨fun _ _ => rfl, fun _ => rfl, fun _ _ _ => rfl⟩

/-! Only the ordinary tensor objects are transported; all morphism types stay explicit. -/
section
variable {C : Type u} [SuperCategory C] [MonoidalCategory (Even C)]
abbrev TensorObjectsAgree (T : SuperFunctor (SuperTensorProduct C C) C) : Prop :=
  ∀ X Y : Even C, evenObj C (T.obj (X, Y)) = X ⊗ Y
abbrev enrichedTensorMap (T : SuperFunctor (SuperTensorProduct C C) C) (h : TensorObjectsAgree T)
    (X X' Y Y' : Even C) :
    SHom C X X' ⊗ SHom C Y Y' ⟶ SHom C (X ⊗ Y : Even C) (X' ⊗ Y' : Even C) :=
  T.map (X, Y) (X', Y') ≫
    eqToHom (congrArg₂ (fun A B : Even C => SHom C A B) (h X Y) (h X' Y'))
abbrev tTensor (T : SuperFunctor (SuperTensorProduct C C) C) (h : TensorObjectsAgree T)
    {X X' Y Y' : Even C} (f : THom C X X') (g : THom C Y Y') :
    THom C (X ⊗ Y : Even C) (X' ⊗ Y' : Even C) := fun a =>
  enrichedTensorMap T h X X' Y Y' a
    (∑ i : ZMod 2, GradedObject.Monoidal.ιTensorObj (SHom C X X') (SHom C Y Y')
      i (a - i) a ((add_comm i (a - i)).trans (sub_add_cancel a i)) (f i ⊗ₜ[ℝ] g (a - i)))
end

end RMod.BrundanEllis
