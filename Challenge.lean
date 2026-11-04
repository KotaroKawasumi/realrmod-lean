import Mathlib

/-!
Brundan--Ellis-oriented declaration surface over real super vector spaces.
The enriching category is fixed. Type-determining fields are explicit;
operation values and laws are construction obligations, specified with ordinary equality.
See docs/BRUNDAN_ELLIS_INTERFACE.md for the paper/Lean composition convention.
-/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped BigOperators TensorProduct
universe u u₁ u₂
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

instance superVecSymmetric : SymmetricCategory SuperVec := by sorry

/-- Both directions of the chosen symmetry are the specified Koszul maps. -/
theorem superVecSymmetric_data (X Y : SuperVec) :
    let S := superVecSymmetric
    (S.braiding X Y).hom = koszulMap X Y ∧
      (S.braiding X Y).inv = koszulMap Y X := by sorry

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
  id X := by sorry
  comp f g := by sorry
  id_comp := by sorry
  comp_id := by sorry
  assoc := by sorry

/-- The total category uses exactly the Hom spaces, identities, and convolution above. -/
theorem totalCategoryCategory_data (C : Type u) [SuperCategory C] :
    (totalCategoryCategory C).toCategoryStruct =
      { Hom := THom C
        id X := evenPoint (eId (C := C) SuperVec (X : C))
        comp := tComp C } := by sorry

instance totalCategoryPreadditive (C : Type u) [SuperCategory C] : Preadditive (TotalCategory C) where
  homGroup X Y := Pi.addCommGroup
  add_comp := by sorry
  comp_add := by sorry

/-- Addition on total morphisms is the pointwise Mathlib additive group structure. -/
theorem totalCategoryPreadditive_data (C : Type u) [SuperCategory C] (X Y : TotalCategory C) :
    (totalCategoryPreadditive C).homGroup X Y =
      (Pi.addCommGroup : AddCommGroup (THom C X Y)) := by sorry

instance totalCategoryLinear (C : Type u) [SuperCategory C] : Linear ℝ (TotalCategory C) where
  homModule X Y := Pi.module (ZMod 2) (fun a => SHom C X Y a) ℝ
  smul_comp := by sorry
  comp_smul := by sorry

/-- Scalar multiplication on total morphisms is the pointwise Mathlib module structure. -/
theorem totalCategoryLinear_data (C : Type u) [SuperCategory C] (X Y : TotalCategory C) :
    (totalCategoryLinear C).homModule X Y =
      (Pi.module (ZMod 2) (fun a => SHom C X Y a) ℝ) := by sorry

instance evenCategoryPreadditive (C : Type u) [SuperCategory C] : Preadditive (Even C) where
  homGroup X Y := Pi.addCommGroup
  add_comp := by sorry
  comp_add := by sorry

/-- Addition on even morphisms is inherited from the specified sVec Hom objects. -/
theorem evenCategoryPreadditive_data (C : Type u) [SuperCategory C] (X Y : Even C) :
    (evenCategoryPreadditive C).homGroup X Y =
      Pi.addCommGroup := by sorry

def grade (C : Type u) [SuperCategory C] (X Y : TotalCategory C) (a : ZMod 2) :
    Submodule ℝ (X ⟶ Y) := by sorry
/-- The grading is exactly support in the specified homogeneous component. -/
theorem grade_data (C : Type u) [SuperCategory C] (X Y : TotalCategory C) (a : ZMod 2) :
    grade C X Y a = (Submodule.pi {a}ᶜ (fun _ => ⊥) : Submodule ℝ (THom C X Y)) := by sorry

abbrev SameParityOrbit (C : Type u) [SuperCategory C] (X Y : TotalCategory C) : Prop :=
  ∃ (a : ZMod 2) (e : X ≅ Y), e.hom ∈ grade C X Y a ∧ e.inv ∈ grade C Y X a

/-! The product enrichment uses Mathlib's chronological order of composition.
Its Hom family is fixed before identities, composition and laws are supplied. -/
def SuperTensorProduct (C : Type u₁) (D : Type u₂) := C × D
instance superTensorProductEnriched (C : Type u₁) (D : Type u₂)
    [SuperCategory C] [SuperCategory D] : SuperCategory (SuperTensorProduct C D) where
  Hom X Y := SHom C X.1 Y.1 ⊗ SHom D X.2 Y.2
  id X := by sorry
  comp X Y Z := by sorry
  id_comp := by sorry
  comp_id := by sorry
  assoc := by sorry

theorem superTensorProductEnriched_data (C : Type u₁) (D : Type u₂)
    [SuperCategory C] [SuperCategory D] :
    let E := superTensorProductEnriched C D
    (∀ X Y, E.Hom X Y = SHom C X.1 Y.1 ⊗ SHom D X.2 Y.2) ∧
    (∀ X, E.id X = (λ_ (𝟙_ SuperVec)).inv ≫ (eId SuperVec X.1 ⊗ₘ eId SuperVec X.2)) ∧
    (∀ X Y Z, E.comp X Y Z = tensorμ _ _ _ _ ≫
      (eComp SuperVec X.1 Y.1 Z.1 ⊗ₘ eComp SuperVec X.2 Y.2 Z.2)) := by sorry

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

/-- Abelian categories supply finite products; use the fixed even additive structure. -/
instance evenFiniteBiproducts (C : Type u) [SuperCategory C] [Abelian (Even C)] :
    HasFiniteBiproducts (Even C) :=
  HasFiniteBiproducts.of_hasFiniteProducts

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

/-! Twists and gauges use Mathlib finite groups, homomorphisms, and units. -/
def realSign (a : ZMod 2) : ℝˣ := if a = 0 then 1 else -1

structure TwistData where
  group : FiniteGrp.{0}
  rho : group →* Multiplicative (ZMod 8)
  nu : group → group → ZMod 2
  omega : group → group → group → ℝˣ

/-- Finite group data and normalized cochains satisfying the signed pentagon equation. -/
structure Twist extends TwistData where
  nu_one_left : ∀ g, nu 1 g = 0
  nu_one_right : ∀ g, nu g 1 = 0
  omega_one₁ : ∀ g h, omega 1 g h = 1
  omega_one₂ : ∀ g h, omega g 1 h = 1
  omega_one₃ : ∀ g h, omega g h 1 = 1
  cocycle : ∀ g h k,
    nu h k + nu (g * h) k + nu g (h * k) + nu g h = 0
  pentagon : ∀ g h k l,
    omega h k l * omega g (h * k) l * omega g h k =
      realSign (nu g h * nu k l) *
        (omega (g * h) k l * omega g h (k * l))

/-! A gauge specifies a move from one source; its target cochains are computed. -/
structure GaugeData (s : TwistData) where
  targetGroup : FiniteGrp.{0}
  phi : s.group ≃* targetGroup
  lam : s.group → ZMod 2
  beta : s.group → s.group → ℝˣ
/-- Normalized gauges retain their raw data and add only the three normalization laws. -/
structure Gauge (s : TwistData) extends GaugeData s where
  lam_one : lam 1 = 0
  beta_one_left : ∀ g, beta 1 g = 1
  beta_one_right : ∀ g, beta g 1 = 1

/-- Compute the target, using the new binary cochain in the signed omega formula. -/
@[implicit_reducible] def gaugeTransformData (s : TwistData) (d : GaugeData s) : TwistData :=
  let nu g h := s.nu g h + d.lam h + d.lam (g * h) + d.lam g
  { group := d.targetGroup
    rho := s.rho.comp d.phi.symm.toMonoidHom
    nu x y := nu (d.phi.symm x) (d.phi.symm y)
    omega x y z :=
      let g := d.phi.symm x
      let h := d.phi.symm y
      let k := d.phi.symm z
      s.omega g h k * (d.beta (g * h) k * d.beta g h) *
        (d.beta h k * d.beta g (h * k))⁻¹ *
        realSign (nu g h * d.lam k + d.lam g * s.nu h k) }

/-- A normalized gauge move lands in Twist; its computational data are fixed below. -/
def gaugeTransform (s : Twist) (g : Gauge s.toTwistData) : Twist := by sorry
/-- The completed move uses exactly the specified cochain formulas. -/
theorem gaugeTransform_data (s : Twist) (g : Gauge s.toTwistData) :
    (gaugeTransform s g).toTwistData = gaugeTransformData s.toTwistData g.toGaugeData := by sorry

/-- Gauge reachability is a relation on valid twists, comparing only their computational data. -/
abbrev GaugeEquivalent (s t : Twist) : Prop :=
  ∃ g : Gauge s.toTwistData, (gaugeTransform s g).toTwistData = t.toTwistData

/-- Construct the real model, including its fusion, split-unit, and weak-pointedness proofs. -/
def realRMod : WeaklyPointedFusionPiSuperCat := by sorry

/-- Construct the completed model assigned to a reference category and a twist. -/
def twistedPullback (C : WeaklyPointedFusionPiSuperCat)
    (hC : IsBrauerWallReference C) (t : Twist) : WeaklyPointedFusionPiSuperCat := by sorry

/-! Classification: reconstruction, the gauge criterion, and normalization to real signs. -/
/-- The constructed real model is a Brauer-Wall reference category. -/
theorem real_isBrauerWallReference : IsBrauerWallReference realRMod := by sorry

/-- Every weakly pointed category is monoidally superequivalent to a twisted pullback. -/
theorem reconstruction (C : WeaklyPointedFusionPiSuperCat)
    (hC : IsBrauerWallReference C) (A : WeaklyPointedFusionPiSuperCat) :
    ∃ t : Twist, MonoidallySuperequivalent A (twistedPullback C hC t) := by sorry

/-- Two constructed models are monoidally superequivalent exactly when their twists are gauge equivalent. -/
theorem equivalence_iff_gauge (C : WeaklyPointedFusionPiSuperCat)
    (hC : IsBrauerWallReference C) (s t : Twist) :
    MonoidallySuperequivalent (twistedPullback C hC s) (twistedPullback C hC t) ↔
      GaugeEquivalent s t := by sorry

/-- Reconstruction can be achieved with every associator scalar equal to a real sign. -/
theorem sign_reconstruction (C : WeaklyPointedFusionPiSuperCat)
    (hC : IsBrauerWallReference C) (A : WeaklyPointedFusionPiSuperCat) :
    ∃ t : Twist, (∀ g h k, t.omega g h k = 1 ∨ t.omega g h k = -1) ∧
      MonoidallySuperequivalent A (twistedPullback C hC t) := by sorry

end RMod.BrundanEllis

/-! Stacking: the reviewed extension of the Brundan--Ellis declaration surface. -/
namespace RMod.BrundanEllis

/-! Finite sums, parity shifts and even retracts specify the completion. -/
def AddPiHull (C : WeaklyPointedFusionPiSuperCat) {I : Type}
    (Z : I → Even C) (X : Even C) : Prop :=
  ∃ (n : ℕ) (i : Fin n → I) (p : Fin n → Bool), Nonempty (Retract X
    (⨁ fun j => if p j then evenObj C (MonoidalPiSuperCategory.pi (C := C)) ⊗ Z (i j)
      else Z (i j)))

/-- The object map fixes Hom types; the morphism formula is specified by evenPair_data. -/
def evenPair {A B D : WeaklyPointedFusionPiSuperCat}
    (F : SuperFunctor (SuperTensorProduct A B) D) : Even A × Even B ⥤ Even D where
  obj X := evenObj D (F.obj (X.1, X.2))
  map {X Y} f := by sorry
  map_id := by sorry
  map_comp := by sorry

theorem evenPair_data {A B D : WeaklyPointedFusionPiSuperCat}
    (F : SuperFunctor (SuperTensorProduct A B) D) :
    (∀ X, (evenPair F).obj X = evenObj D (F.obj (X.1, X.2))) ∧
    (∀ X Y (f : X ⟶ Y), ForgetEnrichment.homTo SuperVec ((evenPair F).map f) =
      (λ_ (𝟙_ SuperVec)).inv ≫
        (ForgetEnrichment.homTo SuperVec f.1 ⊗ₘ ForgetEnrichment.homTo SuperVec f.2) ≫
        F.map (X.1, X.2) (Y.1, Y.2)) := by sorry

/-! Abstract Deligne data; the completion and all-degree compatibility are specified below. -/
def deligne (A B : WeaklyPointedFusionPiSuperCat) : WeaklyPointedFusionPiSuperCat := by sorry
def delignePairing (A B : WeaklyPointedFusionPiSuperCat) :
    SuperFunctor (SuperTensorProduct A B) (deligne A B) := by sorry
def deligneMonoidal (A B : WeaklyPointedFusionPiSuperCat) :
    (evenPair (delignePairing A B)).CoreMonoidal := by sorry

/-- Koszul monoidality, full faithfulness and generation characterize the completed product. -/
theorem deligne_data (A B : WeaklyPointedFusionPiSuperCat) :
    let D := deligne A B
    let F := delignePairing A B
    let M := deligneMonoidal A B
    (∀ X X' Y Y' : Even A × Even B,
      (F.map X X' ⊗ₘ F.map Y Y') ≫
        enrichedTensorMap (C := D) (MonoidalSuperCategory.tensor (C := D))
          MonoidalSuperCategory.tensor_objects _ _ _ _ ≫
        eHomWhiskerLeft SuperVec (C := Even D) _ (M.μIso X' Y').hom =
      tensorμ _ _ _ _ ≫
        (enrichedTensorMap (C := A) (MonoidalSuperCategory.tensor (C := A))
          MonoidalSuperCategory.tensor_objects X.1 X'.1 Y.1 Y'.1 ⊗ₘ
         enrichedTensorMap (C := B) (MonoidalSuperCategory.tensor (C := B))
          MonoidalSuperCategory.tensor_objects X.2 X'.2 Y.2 Y'.2) ≫
        F.map (X ⊗ Y : Even A × Even B) (X' ⊗ Y' : Even A × Even B) ≫
        eHomWhiskerRight SuperVec (C := Even D) (M.μIso X Y).hom _) ∧
    (∀ X Y a, Function.Bijective (F.map X Y a)) ∧
    (∀ X : Even D, AddPiHull D (fun Z => evenObj D (F.obj Z)) X) := by sorry

/-! Labels come from the pullbacks themselves; no separate GMarked category is introduced. -/
abbrev pullback (s : Twist) := twistedPullback realRMod real_isBrauerWallReference s
def pullbackSimple (s : Twist) : s.group → Even (pullback s) := by sorry
theorem pullbackSimple_data (s : Twist) :
    (∀ g, Simple (pullbackSimple s g)) ∧
    (∀ X : Even (pullback s), Simple X →
      ∃ g, SameParityOrbit (pullback s) X (pullbackSimple s g)) ∧
    (∀ g h, SameParityOrbit (pullback s) (pullbackSimple s g) (pullbackSimple s h) ↔ g = h) ∧
    pullbackSimple s 1 = (𝟙_ (Even (pullback s))) ∧
    (∀ g h X, Simple X → Nonempty (Retract X (pullbackSimple s g ⊗ pullbackSimple s h)) →
      SameParityOrbit (pullback s) X (pullbackSimple s (g * h))) ∧
    (∀ g, HasBrauerWallType (pullback s) (pullbackSimple s g) (s.rho g).toAdd) := by sorry

/-! The stack and its inclusion are construction data; their properties are separate targets. -/
def stack (s t : Twist) (h : s.group = t.group) : WeaklyPointedFusionPiSuperCat := by sorry
def stackInclusion (s t : Twist) (h : s.group = t.group) :
    SuperFunctor (stack s t h) (deligne (pullback s) (pullback t)) := by sorry
def stackMonoidal (s t : Twist) (h : s.group = t.group) :
    (stackInclusion s t h).forget.CoreMonoidal := by sorry

/-- A fully faithful monoidal inclusion whose image is precisely the completed diagonal. -/
theorem stack_data (s t : Twist) (h : s.group = t.group) :
    let C := stack s t h
    let D := deligne (pullback s) (pullback t)
    let F := stackInclusion s t h
    let M := stackMonoidal s t h
    (∀ X Y a, Function.Bijective (F.map X Y a)) ∧
    (∀ {X X' Y Y'} (f : THom C X X') (g : THom C Y Y'),
      tComp D (tTensor (C := D) (MonoidalSuperCategory.tensor (C := D)) MonoidalSuperCategory.tensor_objects
        (tMap F f) (tMap F g)) (evenPoint (M.μIso X' Y').hom) =
      tComp D (evenPoint (M.μIso X Y).hom)
        (tMap F (tTensor (C := C) (MonoidalSuperCategory.tensor (C := C))
          MonoidalSuperCategory.tensor_objects f g))) ∧
    (∀ Z : Even D,
      (∃ X : Even C, Nonempty (F.forget.obj X ≅ Z)) ↔
      AddPiHull D (fun g : s.group => evenObj D
        ((delignePairing (pullback s) (pullback t)).obj
          (pullbackSimple s g, pullbackSimple t (h ▸ g)))) Z) := by sorry

/-! A fixed group is a subtype of the existing Twist, not another twist structure.
The equality witnesses only transport indices; gauges must additionally have identity group map. -/
abbrev TwistOn (G : FiniteGrp.{0}) := {s : Twist // s.group = G}
abbrev GaugeEquivalentOn {G : FiniteGrp.{0}} (s t : TwistOn G) : Prop :=
  ∃ d : Gauge s.val.toTwistData, ∃ hd : d.targetGroup = s.val.group,
    (hd ▸ d.phi) = MulEquiv.refl s.val.group ∧
    (gaugeTransform s.val d).toTwistData = t.val.toTwistData

/-! Closed cochains of u. Multiplication in Multiplicative (ZMod 8) means addition mod 8. -/
def bwBit (a : Multiplicative (ZMod 8)) : ZMod 2 := (a.toAdd.val : ZMod 2)
def bwCarry (a b : Multiplicative (ZMod 8)) : ZMod 2 := if 8 ≤ a.toAdd.val + b.toAdd.val then 1 else 0
def bwPrimitive (a : Multiplicative (ZMod 8)) : ZMod 2 := ((a.toAdd.val * (a.toAdd.val + 1) / 2 : ℕ) : ZMod 2)
def cupOne {G : FiniteGrp.{0}} (v z : G → G → ZMod 2) (g h k : G) : ZMod 2 :=
  v (g * h) k * z g h + v g (h * k) * z h k

def twistMulData (s t : Twist) (hG : s.group = t.group) : TwistData :=
  let tRho : s.group →* Multiplicative (ZMod 8) := hG.symm ▸ t.rho
  let tNu : s.group → s.group → ZMod 2 := hG.symm ▸ t.nu
  let tOmega : s.group → s.group → s.group → ℝˣ := hG.symm ▸ t.omega
  let x := fun g => bwBit (s.rho g)
  let y := fun g => bwBit (tRho g)
  let c := fun g h => x g * y h
  { group := s.group
    rho := s.rho * tRho
    nu g h := s.nu g h + tNu g h + c g h
    omega g h k := s.omega g h k * tOmega g h k * realSign
      (cupOne tNu s.nu g h k + cupOne c (fun a b => s.nu a b + tNu a b) g h k +
       bwPrimitive (s.rho g) * y h * y k + x g * (x h * y h) * y k) }

/-- Construct a valid twist with exactly the displayed data; closure is an output obligation. -/
def twistMul {G : FiniteGrp.{0}} (s t : TwistOn G) : TwistOn G := by sorry
theorem twistMul_data {G : FiniteGrp.{0}} (s t : TwistOn G) :
    (twistMul s t).val.toTwistData =
      twistMulData s.val t.val (s.property.trans t.property.symm) := by sorry

/-- Main comparison: the geometric stack is the pullback of the explicitly computed twist. -/
theorem stack_pullback {G : FiniteGrp.{0}} (s t : TwistOn G) :
    MonoidallySuperequivalent (stack s.val t.val (s.property.trans t.property.symm))
      (pullback (twistMul s t).val) := by sorry

/-! Identity gauges, rather than independent relabelings by Aut(G), define the group quotient. -/
theorem gaugeEquivalentOn_equivalence (G : FiniteGrp.{0}) :
    Equivalence (@GaugeEquivalentOn G) := by sorry
def twistSetoid (G : FiniteGrp.{0}) : Setoid (TwistOn G) :=
  ⟨GaugeEquivalentOn, gaugeEquivalentOn_equivalence G⟩
abbrev TwistClass (G : FiniteGrp.{0}) := Quot (@GaugeEquivalentOn G)
abbrev twistClass {G : FiniteGrp.{0}} (s : TwistOn G) : TwistClass G := Quot.mk _ s

/-! The neutral twist and inverse cochains specify the remaining group operations. -/
def twistUnit (G : FiniteGrp.{0}) : TwistOn G := by sorry
theorem twistUnit_data (G : FiniteGrp.{0}) :
    (twistUnit G).val.toTwistData = ⟨G, 1, fun _ _ => 0, fun _ _ _ => 1⟩ := by sorry

/-- With these cochains, the displayed product of s with its inverse is the neutral twist. -/
def twistInvData (s : Twist) : TwistData :=
  let x := fun g => bwBit (s.rho g)
  let v := fun g h => s.nu g h + x g * x h
  { group := s.group
    rho := s.rho⁻¹
    nu := v
    omega g h k := (s.omega g h k)⁻¹ * realSign
      (cupOne v s.nu g h k + (bwPrimitive (s.rho g) + x g) * x h * x k) }
def twistInv {G : FiniteGrp.{0}} (s : TwistOn G) : TwistOn G := by sorry
theorem twistInv_data {G : FiniteGrp.{0}} (s : TwistOn G) :
    (twistInv s).val.toTwistData = twistInvData s.val := by sorry

/-- Construct a commutative group with the specified multiplication, unit, and inverse. -/
instance twistClassCommGroup (G : FiniteGrp.{0}) : CommGroup (TwistClass G) := by sorry
theorem twistClassCommGroup_data {G : FiniteGrp.{0}} (s t : TwistOn G) :
    twistClass s * twistClass t = twistClass (twistMul s t) ∧
      (1 : TwistClass G) = twistClass (twistUnit G) ∧
      (twistClass s)⁻¹ = twistClass (twistInv s) := by sorry

/-! SHReal is precisely the degree-zero subgroup: the same normalized (nu, omega) and gauges.
The formula above restricts to the Gu--Wen product with sign (nu_t cup_1 nu_s). -/
def degree (G : FiniteGrp.{0}) : TwistClass G →* (G →* Multiplicative (ZMod 8)) := by sorry
theorem degree_data {G : FiniteGrp.{0}} (s : TwistOn G) :
    degree G (twistClass s) = (s.property ▸ s.val.rho) := by sorry
abbrev SHReal (G : FiniteGrp.{0}) := (degree G).ker

/-- A split extension for each finite G; no natural choice of splitting is required. -/
def stackingSplit (G : FiniteGrp.{0}) :
    TwistClass G ≃* ((G →* Multiplicative (ZMod 8)) × SHReal G) := by sorry
theorem stackingSplit_data {G : FiniteGrp.{0}} (z : TwistClass G) (a : SHReal G) :
    (stackingSplit G z).1 = degree G z ∧
      stackingSplit G (a : TwistClass G) = (1, a) := by sorry

end RMod.BrundanEllis
