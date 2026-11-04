import Mathlib
import RMod.Hierarchy.Instances.SuperVecSymmetric

/-! Real graded vector spaces and their enriched total composition. -/
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped BigOperators TensorProduct
universe u u₁ u₂
attribute [-instance] RMod.Legacy.moduleCatHasInitial
namespace RMod

/-! Real super vector spaces with the graded tensor product and Koszul symmetry. -/
@[implicit_reducible] def SuperVec := GradedObject (ZMod 2) (ModuleCat.{0} ℝ)
instance : Category SuperVec := GradedObject.categoryOfGradedObjects (ZMod 2)
instance : MonoidalCategory SuperVec := GradedObject.monoidalCategory
def koszulMap (X Y : SuperVec) (a : ZMod 2) : (X ⊗ Y) a ⟶ (Y ⊗ X) a :=
  GradedObject.Monoidal.tensorObjDesc fun i j hij =>
    ((-1 : ℝ) ^ (i * j).val) •
      ((β_ (X i) (Y j)).hom ≫
        GradedObject.Monoidal.ιTensorObj Y X j i a ((add_comm j i).trans hij))

instance superVecSymmetric : SymmetricCategory SuperVec where
  braiding X Y := ⟨koszulMap X Y, koszulMap Y X, Legacy.koszulMap_comp X Y, Legacy.koszulMap_comp Y X⟩
  braiding_naturality_left := Legacy.koszul_naturality_left
  braiding_naturality_right := Legacy.koszul_naturality_right
  hexagon_forward := Legacy.koszul_hexagon_forward
  hexagon_reverse := Legacy.koszul_hexagon_reverse
  symmetry := Legacy.koszulMap_comp

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

end RMod
