import RMod.Enriched.Surface
import RMod.Enriched.TotalLaws
import RMod.Statement.GaugeLegacy

/-! The concrete SuperVec interface and the completed twist and gauge operations. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped BigOperators TensorProduct
universe u u₁ u₂ v w
namespace RMod

@[implicit_reducible] def TotalCategory (C : Type u) [SuperCategory C] : Type u := C
def totalObj (C : Type u) [SuperCategory C] (X : C) : TotalCategory C := X
instance totalCategoryCategory (C : Type u) [SuperCategory C] : Category.{0} (TotalCategory C) where
  Hom := THom C
  id X := evenPoint (eId (C := C) SuperVec (X : C))
  comp := tComp C
  id_comp := fun {_ _} f => EnrichedSupport.tComp_id_left C f
  comp_id := fun {_ _} f => EnrichedSupport.tComp_id_right C f
  assoc := fun {_ _ _ _} f g h => EnrichedSupport.tComp_assoc C f g h

/-- The total category uses exactly the Hom spaces, identities, and convolution above. -/
theorem totalCategoryCategory_data (C : Type u) [SuperCategory C] :
    (totalCategoryCategory C).toCategoryStruct =
      { Hom := THom C
        id X := evenPoint (eId (C := C) SuperVec (X : C))
        comp := tComp C } := rfl

instance totalCategoryPreadditive (C : Type u) [SuperCategory C] : Preadditive (TotalCategory C) where
  homGroup X Y := Pi.addCommGroup
  add_comp := fun _ _ _ f g h => EnrichedSupport.tComp_add_left C f g h
  comp_add := fun _ _ _ f g h => EnrichedSupport.tComp_add_right C f g h

/-- Addition on total morphisms is the pointwise Mathlib additive group structure. -/
theorem totalCategoryPreadditive_data (C : Type u) [SuperCategory C] (X Y : TotalCategory C) :
    HEq ((totalCategoryPreadditive C).homGroup X Y)
      (Pi.addCommGroup : AddCommGroup (THom C X Y)) := HEq.rfl

instance totalCategoryLinear (C : Type u) [SuperCategory C] : Linear ℝ (TotalCategory C) where
  homModule X Y := Pi.module (ZMod 2) (fun a => SHom C X Y a) ℝ
  smul_comp := fun _ _ _ r f g => EnrichedSupport.tComp_smul_left C r f g
  comp_smul := fun _ _ _ f r g => EnrichedSupport.tComp_smul_right C r f g

/-- Scalar multiplication on total morphisms is the pointwise Mathlib module structure. -/
theorem totalCategoryLinear_data (C : Type u) [SuperCategory C] (X Y : TotalCategory C) :
    HEq ((totalCategoryLinear C).homModule X Y)
      (Pi.module (ZMod 2) (fun a => SHom C X Y a) ℝ) := HEq.rfl

section
local instance : Preadditive SuperVec := Legacy.superVecPreadditive
local instance : MonoidalPreadditive SuperVec := Legacy.superVecMonoidalPreadditive

instance evenCategoryPreadditive (C : Type u) [SuperCategory C] : Preadditive (Even C) where
  homGroup X Y := Pi.addCommGroup
  add_comp X Y Z f g h := by
    change (𝟙_ SuperVec ⟶ SHom C X Y) at f g
    change (𝟙_ SuperVec ⟶ SHom C Y Z) at h
    change (λ_ (𝟙_ SuperVec)).inv ≫ ((f + g) ⊗ₘ h) ≫ eComp SuperVec X Y Z =
      ((λ_ (𝟙_ SuperVec)).inv ≫ (f ⊗ₘ h) ≫ eComp SuperVec X Y Z) +
      ((λ_ (𝟙_ SuperVec)).inv ≫ (g ⊗ₘ h) ≫ eComp SuperVec X Y Z)
    rw [MonoidalPreadditive.add_tensor, Preadditive.add_comp, Preadditive.comp_add]
  comp_add X Y Z f g h := by
    change (𝟙_ SuperVec ⟶ SHom C X Y) at f
    change (𝟙_ SuperVec ⟶ SHom C Y Z) at g h
    change (λ_ (𝟙_ SuperVec)).inv ≫ (f ⊗ₘ (g + h)) ≫ eComp SuperVec X Y Z =
      ((λ_ (𝟙_ SuperVec)).inv ≫ (f ⊗ₘ g) ≫ eComp SuperVec X Y Z) +
      ((λ_ (𝟙_ SuperVec)).inv ≫ (f ⊗ₘ h) ≫ eComp SuperVec X Y Z)
    rw [MonoidalPreadditive.tensor_add, Preadditive.add_comp, Preadditive.comp_add]

/-- Addition on even morphisms is inherited from the specified sVec Hom objects. -/
theorem evenCategoryPreadditive_data (C : Type u) [SuperCategory C] (X Y : Even C) :
    (evenCategoryPreadditive C).homGroup X Y =
      Pi.addCommGroup := rfl
end

/-- The specified identification of total morphisms with both homogeneous components. -/
def totalHom {C : Type u} [SuperCategory C] {X Y : TotalCategory C}
    (f : THom C X Y) : X ⟶ Y :=
  cast (congrArg (fun d : CategoryStruct (TotalCategory C) => d.Hom X Y)
    (totalCategoryCategory_data C).symm) f

def grade (C : Type u) [SuperCategory C] (X Y : TotalCategory C) (a : ZMod 2) :
    Submodule ℝ (X ⟶ Y) := Submodule.pi {a}ᶜ (fun _ => ⊥)
/-- The grading is exactly support in the specified homogeneous component. -/
theorem grade_data (C : Type u) [SuperCategory C] (X Y : TotalCategory C) (a : ZMod 2) :
    HEq (grade C X Y a) (Submodule.pi {a}ᶜ (fun _ => ⊥) : Submodule ℝ (THom C X Y)) := HEq.rfl

abbrev SameParityOrbit (C : Type u) [SuperCategory C] (X Y : TotalCategory C) : Prop :=
  ∃ (a : ZMod 2) (e : X ≅ Y), e.hom ∈ grade C X Y a ∧ e.inv ∈ grade C Y X a

/-! A parity shift is an odd graded natural isomorphism, with an explicit inverse. -/
structure ParityShift (C : Type u) [SuperCategory C] where
  functor : SuperFunctor C C
  hom : GradedNatTrans ((Center.ofBraided SuperVec).obj oddLine)
    (EnrichedFunctor.id SuperVec C) functor
  inv : ∀ X, oddLine ⟶ SHom C (functor.obj X) X
  hom_inv : ∀ X, tComp C (homogeneousPoint 1 (hom.app X))
    (homogeneousPoint 1 (inv X)) = evenPoint (eId SuperVec X)
  inv_hom : ∀ X, tComp C (homogeneousPoint 1 (inv X))
    (homogeneousPoint 1 (hom.app X)) = evenPoint (eId SuperVec (functor.obj X))
class PiSuperCategory (C : Type u) [SuperCategory C] where
  parityShift : ParityShift C

/-! Rigidity and finite biproducts use Mathlib's classes; split unit uses the total algebra. -/
abbrev IsSplitUnit (C : Type u) [SuperCategory C] [MonoidalCategory (Even C)] : Prop :=
  Nonempty (CategoryTheory.End (totalObj C (𝟙_ (Even C))) ≃ₐ[ℝ] ℝ)

/-- Abelian categories supply finite products; use the fixed even additive structure. -/
instance evenFiniteBiproducts (C : Type u) [SuperCategory C] [Abelian (Even C)] :
    HasFiniteBiproducts (Even C) :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- Fusion adds only conditions on the given enriched, Pi and monoidal structures. -/
class FusionPiSuperCategory (C : Type u) [SuperCategory C] [PiSuperCategory C]
    [MonoidalCategory (Even C)] [MonoidalEnrichedCategory SuperVec C]
    [RigidCategory (Even C)] [Abelian (Even C)] : Prop where
  hom_finite : ∀ X Y a, FiniteDimensional ℝ (SHom C X Y a)
  semisimple : ∀ X : Even C, ∃ (n : ℕ) (S : Fin n → Even C),
    (∀ i, Simple (S i)) ∧ Nonempty (X ≅ ⨁ S)
  finite_simples : ∃ (n : ℕ) (S : Fin n → Even C),
    (∀ i, Simple (S i)) ∧ ∀ X : Even C, Simple X → ∃ i, SameParityOrbit C X (S i)
  simple_unit : Simple (𝟙_ (Even C))

/-- In ExactPairing X Y, Y is a Mathlib right dual (an EGNO left dual). -/
def IsWeaklyInvertible (C : Type u) [SuperCategory C] [PiSuperCategory C]
    [MonoidalCategory (Even C)] [HasFiniteBiproducts (Even C)] (X : Even C) : Prop :=
  ∃ Y : Even C, Nonempty (ExactPairing X Y) ∧
    ∃ p q : ℕ, Nonempty (X ⊗ Y ≅ ⨁ (Sum.elim
      (fun _ : Fin p => 𝟙_ (Even C))
      (fun _ : Fin q => evenObj C ((PiSuperCategory.parityShift (C := C)).functor.obj (𝟙_ (Even C))))))
def IsWeaklyPointed (C : Type u) [SuperCategory C] [PiSuperCategory C]
    [MonoidalCategory (Even C)] [HasFiniteBiproducts (Even C)] : Prop :=
  ∀ X : Even C, Simple X → IsWeaklyInvertible C X

/-- Weak pointedness adds only the split-unit and weak-invertibility conditions. -/
class WeaklyPointedFusionPiSuperCategory (C : Type u) [SuperCategory C] [PiSuperCategory C]
    [MonoidalCategory (Even C)] [MonoidalEnrichedCategory SuperVec C]
    [RigidCategory (Even C)] [Abelian (Even C)] [FusionPiSuperCategory C] : Prop where
  splitUnit : IsSplitUnit C
  weaklyPointed : IsWeaklyPointed C

/-! Equivalences use Mathlib's strong monoidal coherence on the even category.
Their unit, counit and tensor comparison still commute with arbitrary total morphisms. -/
section Equivalence
variable (C : Type u₁) (D : Type u₂) [SuperCategory C] [SuperCategory D]
  [MonoidalCategory (Even C)] [MonoidalCategory (Even D)]
  [MonoidalEnrichedCategory SuperVec C] [MonoidalEnrichedCategory SuperVec D]

/-- The super interface is the degree-zero generic enriched equivalence. -/
abbrev MonoidalSuperequivalence := MonoidalEnrichedEquivalence SuperVec C D

abbrev MonoidallySuperequivalent : Prop := Nonempty (MonoidalSuperequivalence C D)
end Equivalence

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
  [piSuperCategory : PiSuperCategory carrier]
  [monoidalCategory : MonoidalCategory (Even carrier)]
  [monoidalEnrichedCategory : MonoidalEnrichedCategory SuperVec carrier]
  [rigidCategory : RigidCategory (Even carrier)]
  [abelian : Abelian (Even carrier)]
  [fusion : FusionPiSuperCategory carrier]
  [weaklyPointed : WeaklyPointedFusionPiSuperCategory carrier]

instance : CoeSort WeaklyPointedFusionPiSuperCat (Type) := ⟨WeaklyPointedFusionPiSuperCat.carrier⟩
attribute [instance] WeaklyPointedFusionPiSuperCat.superCategory
  WeaklyPointedFusionPiSuperCat.piSuperCategory WeaklyPointedFusionPiSuperCat.monoidalCategory
  WeaklyPointedFusionPiSuperCat.monoidalEnrichedCategory WeaklyPointedFusionPiSuperCat.rigidCategory
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

/-! Reuse the proven gauge action after copying only its raw group and cochain data. -/
private def twistToOld (s : Twist) : Classification.Twist :=
  ⟨⟨s.toTwistData.group, s.toTwistData.rho, s.toTwistData.nu, s.toTwistData.omega⟩,
    ⟨s.nu_one_left, s.nu_one_right, s.omega_one₁, s.omega_one₂, s.omega_one₃,
      s.cocycle, s.pentagon⟩⟩

private def gaugeToRevision (s : Twist) (g : Gauge s.toTwistData) : GaugeRevision.Gauge (twistToOld s).data :=
  ⟨⟨g.targetGroup, g.phi, g.lam, g.beta⟩,
    ⟨g.lam_one, g.beta_one_left, g.beta_one_right⟩⟩

/-- A normalized gauge move lands in Twist; its computational data are fixed below. -/
def gaugeTransform (s : Twist) (g : Gauge s.toTwistData) : Twist :=
  let h := GaugeRevision.gaugeTransformLaws (twistToOld s) (gaugeToRevision s g)
  { toTwistData := gaugeTransformData s.toTwistData g.toGaugeData
    nu_one_left := h.nu_one_left
    nu_one_right := h.nu_one_right
    omega_one₁ := h.omega_one₁
    omega_one₂ := h.omega_one₂
    omega_one₃ := h.omega_one₃
    cocycle := h.cocycle
    pentagon := h.pentagon }
/-- The completed move uses exactly the specified cochain formulas. -/
theorem gaugeTransform_data (s : Twist) (g : Gauge s.toTwistData) :
    (gaugeTransform s g).toTwistData = gaugeTransformData s.toTwistData g.toGaugeData := rfl

/-- Gauge reachability is a relation on valid twists, comparing only their computational data. -/
abbrev GaugeEquivalent (s t : Twist) : Prop :=
  ∃ g : Gauge s.toTwistData, (gaugeTransform s g).toTwistData = t.toTwistData

end RMod
