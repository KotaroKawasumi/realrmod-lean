import RMod.BrundanEllis.EvenBiproducts

/-! Fixed definitions shared with the Brundan--Ellis Challenge draft.
These are the declaration-surface forms allowed by the Data--Laws exception.
No instance construction or classification proof is introduced in this file. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped BigOperators TensorProduct
universe u u₁ u₂
namespace RMod.BrundanEllis

/-! Ordinary coherence is reused; naturality is imposed on all super morphisms. -/
class MonoidalSuperCategory (C : Type u) [SuperCategory C] [MonoidalCategory (Even C)] where
  tensor : SuperFunctor (SuperTensorProduct C C) C
  tensor_objects : TensorObjectsAgree tensor
  tensor_even : ∀ {X X' Y Y' : Even C} (f : X ⟶ X') (g : Y ⟶ Y'),
    (λ_ (𝟙_ SuperVec)).inv ≫
      (ForgetEnrichment.homTo SuperVec f ⊗ₘ ForgetEnrichment.homTo SuperVec g) ≫
      enrichedTensorMap tensor tensor_objects X X' Y Y' =
        ForgetEnrichment.homTo SuperVec (f ⊗ₘ g)
  associator_naturality : ∀ {X X' Y Y' Z Z' : Even C}
      (f : THom C X X') (g : THom C Y Y') (h : THom C Z Z'),
    tComp C (tTensor tensor tensor_objects (tTensor tensor tensor_objects f g) h)
      (evenPoint (ForgetEnrichment.homTo SuperVec (α_ X' Y' Z').hom)) =
    tComp C (evenPoint (ForgetEnrichment.homTo SuperVec (α_ X Y Z).hom))
      (tTensor tensor tensor_objects f (tTensor tensor tensor_objects g h))
  left_naturality : ∀ {X Y : Even C} (f : THom C X Y),
    tComp C (tTensor tensor tensor_objects (evenPoint (eId (C := C) SuperVec (𝟙_ (Even C)))) f)
      (evenPoint (ForgetEnrichment.homTo SuperVec (λ_ Y).hom)) =
    tComp C (evenPoint (ForgetEnrichment.homTo SuperVec (λ_ X).hom)) f
  right_naturality : ∀ {X Y : Even C} (f : THom C X Y),
    tComp C (tTensor tensor tensor_objects f (evenPoint (eId (C := C) SuperVec (𝟙_ (Even C)))))
      (evenPoint (ForgetEnrichment.homTo SuperVec (ρ_ Y).hom)) =
    tComp C (evenPoint (ForgetEnrichment.homTo SuperVec (ρ_ X).hom)) f

/-! Definition 1.12: a parity object with an odd isomorphism to the unit.
The functor pi tensor - is derived in the proof library, not stored as extra input. -/
class MonoidalPiSuperCategory (C : Type u) [SuperCategory C] [MonoidalCategory (Even C)] where
  pi : C
  hom : oddLine ⟶ SHom C pi (𝟙_ (Even C))
  inv : oddLine ⟶ SHom C (𝟙_ (Even C)) pi
  hom_inv : tComp C (homogeneousPoint 1 hom) (homogeneousPoint 1 inv) =
    evenPoint (eId SuperVec pi)
  inv_hom : tComp C (homogeneousPoint 1 inv) (homogeneousPoint 1 hom) =
    evenPoint (eId (C := C) SuperVec (𝟙_ (Even C)))

/-! Rigidity and finite biproducts use Mathlib's classes; split unit uses the total algebra. -/
abbrev IsSplitUnit (C : Type u) [SuperCategory C] [MonoidalCategory (Even C)] : Prop :=
  Nonempty (CategoryTheory.End (totalObj C (𝟙_ (Even C))) ≃ₐ[ℝ] ℝ)

/-- Fusion adds only conditions on the given enriched, Pi and monoidal structures. -/
class FusionPiSuperCategory (C : Type u) [SuperCategory C] [MonoidalCategory (Even C)] [MonoidalPiSuperCategory C] [MonoidalSuperCategory C]
    [RigidCategory (Even C)] [Abelian (Even C)] : Prop where
  hom_finite : ∀ X Y a, FiniteDimensional ℝ (SHom C X Y a)
  semisimple : ∀ X : Even C, ∃ (n : ℕ) (S : Fin n → Even C),
    (∀ i, Simple (S i)) ∧ Nonempty (X ≅ ⨁ S)
  finite_simples : ∃ (n : ℕ) (S : Fin n → Even C),
    (∀ i, Simple (S i)) ∧ ∀ X : Even C, Simple X → ∃ i, SameParityOrbit C X (S i)
  simple_unit : Simple (𝟙_ (Even C))

attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

/-- Use the selected Mathlib right dual (an EGNO left dual): X tensor Xᘁ is a sum of units and pi. -/
def IsWeaklyInvertible (C : Type u) [SuperCategory C] [MonoidalCategory (Even C)]
    [MonoidalPiSuperCategory C] [RigidCategory (Even C)] [HasFiniteBiproducts (Even C)]
    (X : Even C) : Prop :=
  ∃ p q : ℕ, Nonempty (X ⊗ Xᘁ ≅
    (⨁ fun _ : Fin p => 𝟙_ (Even C)) ⊞
    (⨁ fun _ : Fin q => evenObj C (MonoidalPiSuperCategory.pi (C := C))))
def IsWeaklyPointed (C : Type u) [SuperCategory C] [MonoidalCategory (Even C)]
    [MonoidalPiSuperCategory C] [RigidCategory (Even C)] [HasFiniteBiproducts (Even C)] : Prop :=
  ∀ X : Even C, Simple X → IsWeaklyInvertible C X

/-- Weak pointedness adds only the split-unit and weak-invertibility conditions. -/
class WeaklyPointedFusionPiSuperCategory (C : Type u) [SuperCategory C] [MonoidalCategory (Even C)] [MonoidalPiSuperCategory C] [MonoidalSuperCategory C]
    [RigidCategory (Even C)] [Abelian (Even C)] [FusionPiSuperCategory C] : Prop where
  splitUnit : IsSplitUnit C
  weaklyPointed : IsWeaklyPointed C

/-! Strong monoidal superequivalence, with even comparisons natural in every degree. -/
def tMap {C : Type u₁} {D : Type u₂} [SuperCategory C] [SuperCategory D]
    (F : SuperFunctor C D) {X Y : C} (f : THom C X Y) : THom D (F.obj X) (F.obj Y) :=
  fun a => F.map X Y a (f a)
section
variable (C : Type u₁) (D : Type u₂) [SuperCategory C] [SuperCategory D]
  [MonoidalCategory (Even C)] [MonoidalCategory (Even D)]
  [MC : MonoidalSuperCategory C] [MD : MonoidalSuperCategory D]
structure MonoidalSuperequivalence where
  forward : SuperFunctor C D
  backward : SuperFunctor D C
  monoidal : forward.forget.CoreMonoidal
  unit : 𝟭 (Even C) ≅ forward.forget ⋙ backward.forget
  counit : backward.forget ⋙ forward.forget ≅ 𝟭 (Even D)
  unit_natural : ∀ {X Y} (f : THom C X Y),
    tComp C f (evenPoint (unit.hom.app Y)) =
      tComp C (evenPoint (unit.hom.app X)) (tMap backward (tMap forward f))
  counit_natural : ∀ {X Y} (f : THom D X Y),
    tComp D (tMap forward (tMap backward f)) (evenPoint (counit.hom.app Y)) =
      tComp D (evenPoint (counit.hom.app X)) f
  tensor_natural : ∀ {X X' Y Y'} (f : THom C X X') (g : THom C Y Y'),
    tComp D (tTensor MD.tensor MD.tensor_objects (tMap forward f) (tMap forward g))
      (evenPoint (monoidal.μIso X' Y').hom) =
    tComp D (evenPoint (monoidal.μIso X Y).hom)
      (tMap forward (tTensor MC.tensor MC.tensor_objects f g))
abbrev MonoidallySuperequivalent : Prop := Nonempty (MonoidalSuperequivalence C D)
end

/-! Brauer–Wall predicates concern carriers and their given structures, not bundled projections. -/
abbrev HasBrauerWallType (C : Type u) [SuperCategory C] [HasFiniteBiproducts (Even C)]
    (X : Even C) (r : ZMod 8) : Prop :=
  let Q := QuadraticMap.weightedSumSquares ℝ (fun _ : Fin r.val => (-1 : ℝ))
  ∃ (n : ℕ) (S : Fin n → Even C), 0 < n ∧
    (∀ i, SameParityOrbit C X (S i)) ∧
    ∃ e : CliffordAlgebra Q ≃ₐ[ℝ] CategoryTheory.End (totalObj C (biproduct (C := Even C) S)),
      ∀ a x, x ∈ CliffordAlgebra.evenOdd Q a ↔
        e x ∈ grade C (biproduct (C := Even C) S) (biproduct (C := Even C) S) a
/-- The eight real Brauer–Wall types classify the simple parity orbits. -/
structure IsBrauerWallReference (C : Type u) [SuperCategory C]
    [HasFiniteBiproducts (Even C)] : Prop where
  simple_type : ∀ X : Even C, Simple X → ∃! r, HasBrauerWallType C X r
  realizes_type : ∀ r, ∃ X : Even C, Simple X ∧ HasBrauerWallType C X r
  type_detects_orbit : ∀ (X Y : Even C) r,
    Simple X → Simple Y → HasBrauerWallType C X r →
    (HasBrauerWallType C Y r ↔ SameParityOrbit C X Y)

/-! Only the classification boundary needs categories as values. The small-carrier universe
matches the original classification; all interfaces above are universe-polymorphic. -/
structure WeaklyPointedFusionPiSuperCat where
  carrier : Type
  [superCategory : SuperCategory carrier]
  [monoidalCategory : MonoidalCategory (Even carrier)]
  [piSuperCategory : MonoidalPiSuperCategory carrier]
  [monoidalSuperCategory : MonoidalSuperCategory carrier]
  [rigidCategory : RigidCategory (Even carrier)]
  [abelian : Abelian (Even carrier)]
  [fusion : FusionPiSuperCategory carrier]
  [weaklyPointed : WeaklyPointedFusionPiSuperCategory carrier]

instance : CoeSort WeaklyPointedFusionPiSuperCat (Type) := ⟨WeaklyPointedFusionPiSuperCat.carrier⟩
attribute [instance] WeaklyPointedFusionPiSuperCat.superCategory
  WeaklyPointedFusionPiSuperCat.piSuperCategory WeaklyPointedFusionPiSuperCat.monoidalCategory
  WeaklyPointedFusionPiSuperCat.monoidalSuperCategory WeaklyPointedFusionPiSuperCat.rigidCategory
  WeaklyPointedFusionPiSuperCat.abelian
  WeaklyPointedFusionPiSuperCat.fusion
  WeaklyPointedFusionPiSuperCat.weaklyPointed

end RMod.BrundanEllis
