import RMod.Hierarchy.Instances.SuperTensorProduct
import RMod.Hierarchy.Instances.EvenLinear
import RMod.Hierarchy.Instances.TotalCategory

/-!
# Implementations of the fixed public definitions

These declarations share one module, as in Challenge, so Lean's auxiliary
proof declarations are generated in the same order. The established library
supplies the laws; Challenge is never imported.
-/

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped BigOperators TensorProduct
-- Use Mathlib's initial-object instance, as in the Mathlib-only Challenge.
attribute [-instance] RMod.Legacy.moduleCatHasInitial

namespace RMod.StatementLegacy

/-! Real super vector spaces with the graded tensor product and Koszul symmetry. -/
@[implicit_reducible] def SuperVec := GradedObject (ZMod 2) (ModuleCat.{0} ℝ)
instance : Category SuperVec := GradedObject.categoryOfGradedObjects (ZMod 2)
instance : MonoidalCategory SuperVec := GradedObject.monoidalCategory
instance superVecPreadditive : Preadditive SuperVec where
  homGroup X Y := Pi.addCommGroup
  add_comp := Legacy.superVecPreadditive.add_comp
  comp_add := Legacy.superVecPreadditive.comp_add
/-- Addition on graded maps is the pointwise Mathlib additive group structure. -/
theorem superVecPreadditive_data (X Y : SuperVec) :
    superVecPreadditive.homGroup X Y =
      Pi.addCommGroup := rfl
instance superVecLinear : Linear ℝ SuperVec where
  homModule X Y := Pi.module (ZMod 2) (fun a => X a ⟶ Y a) ℝ
  smul_comp := Legacy.superVecLinear.smul_comp
  comp_smul := Legacy.superVecLinear.comp_smul
/-- Scalar multiplication on graded maps is the pointwise Mathlib module structure. -/
theorem superVecLinear_data (X Y : SuperVec) :
    HEq (superVecLinear.homModule X Y)
      (Pi.module (ZMod 2) (fun a => X a ⟶ Y a) ℝ) := HEq.rfl

def koszulMap (X Y : SuperVec) : X ⊗ Y ⟶ Y ⊗ X := fun a =>
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

abbrev koszulBraiding (X Y : SuperVec) : X ⊗ Y ≅ Y ⊗ X := β_ X Y
/-- Both directions of the chosen symmetry are the specified Koszul maps. -/
theorem superVecSymmetric_braiding (X Y : SuperVec) :
    (koszulBraiding X Y).hom = koszulMap X Y ∧
      (koszulBraiding X Y).inv = koszulMap Y X := ⟨rfl, rfl⟩

abbrev oddLine : SuperVec :=
  (GradedObject.single (1 : ZMod 2)).obj (ModuleCat.of ℝ ℝ)

/-! Reuse Mathlib's bundled enriched categories and enriched functors directly. -/
abbrev Supercategory := EnrichedCat.{0, 1, 0} SuperVec
abbrev Superfunctor (C D : Supercategory) := EnrichedFunctor SuperVec C D
abbrev SHom (C : Supercategory) (X Y : C) : SuperVec := X ⟶[SuperVec] Y
abbrev Even (C : Supercategory) := ForgetEnrichment SuperVec C
def evenObj (C : Supercategory) (X : C) : Even C := ForgetEnrichment.of SuperVec X
abbrev EHom (C : Supercategory) (X Y : C) := 𝟙_ SuperVec ⟶ SHom C X Y

/-! The former presentation retains exactly the same enriched operations. -/
def toLegacySupercategory (C : Supercategory) : Legacy.Supercategory where
  data := { Obj := C, Hom := SHom C, id := eId SuperVec, comp := eComp SuperVec }
  laws := {
    id_comp := e_id_comp SuperVec
    comp_id := e_comp_id SuperVec
    assoc := e_assoc SuperVec }

/-! Total Hom spaces combine both graded components of the specified enrichment. -/
abbrev THom (d : Supercategory) (X Y : d) :=
  (a : ZMod 2) → SHom d X Y a
def homogeneousPoint {V : SuperVec} (a : ZMod 2)
    (f : (GradedObject.single a).obj (ModuleCat.of ℝ ℝ) ⟶ V) : (b : ZMod 2) → V b :=
  fun b => if h : b = a then
    f b ((GradedObject.singleObjApplyIsoOfEq a (ModuleCat.of ℝ ℝ) b h).inv 1) else 0
def evenPoint {V : SuperVec} (f : 𝟙_ SuperVec ⟶ V) := homogeneousPoint 0 f
def tComp (d : Supercategory) {X Y Z : d}
    (f : THom d X Y) (g : THom d Y Z) : THom d X Z := fun a =>
  ∑ i : ZMod 2, eComp SuperVec (X : d) Y Z a
    (GradedObject.Monoidal.ιTensorObj (SHom d X Y) (SHom d Y Z)
      i (a - i) a ((add_comm i (a - i)).trans (sub_add_cancel a i)) (f i ⊗ₜ[ℝ] g (a - i)))

@[implicit_reducible] def TotalCategory (C : Supercategory) : Type := C
def totalObj (C : Supercategory) (X : C) : TotalCategory C := X
@[implicit_reducible] def totalCategoryStruct (C : Supercategory) : CategoryStruct (TotalCategory C) where
  Hom := THom C
  id X := evenPoint (eId (C := C) SuperVec (X : C))
  comp := tComp C
instance totalCategoryCategory (C : Supercategory) : Category (TotalCategory C) where
  toCategoryStruct := totalCategoryStruct C
  id_comp := fun {_ _} f => Legacy.tComp_id_left (toLegacySupercategory C) f
  comp_id := fun {_ _} f => Legacy.tComp_id_right (toLegacySupercategory C) f
  assoc := fun {_ _ _ _} f g h => Legacy.tComp_assoc (toLegacySupercategory C) f g h
/-- The total category uses exactly the Hom spaces, identities, and convolution above. -/
theorem totalCategoryCategory_data (C : Supercategory) :
    (totalCategoryCategory C).toCategoryStruct = totalCategoryStruct C := rfl

instance totalCategoryPreadditive (C : Supercategory) : Preadditive (TotalCategory C) where
  homGroup X Y := Pi.addCommGroup
  add_comp := fun _ _ _ f g h => Legacy.tComp_add_left (toLegacySupercategory C).data f g h
  comp_add := fun _ _ _ f g h => Legacy.tComp_add_right (toLegacySupercategory C).data f g h
/-- Addition on total morphisms is the pointwise Mathlib additive group structure. -/
theorem totalCategoryPreadditive_data (C : Supercategory) (X Y : TotalCategory C) :
    (totalCategoryPreadditive C).homGroup X Y =
      Pi.addCommGroup := rfl
instance totalCategoryLinear (C : Supercategory) : Linear ℝ (TotalCategory C) where
  homModule X Y := Pi.module (ZMod 2) (fun a => SHom C X Y a) ℝ
  smul_comp := fun _ _ _ r f g => Legacy.tComp_smul_left (toLegacySupercategory C).data r f g
  comp_smul := fun _ _ _ f r g => Legacy.tComp_smul_right (toLegacySupercategory C).data r f g
/-- Scalar multiplication on total morphisms is the pointwise Mathlib module structure. -/
theorem totalCategoryLinear_data (C : Supercategory) (X Y : TotalCategory C) :
    HEq ((totalCategoryLinear C).homModule X Y)
      (Pi.module (ZMod 2) (fun a => SHom C X Y a) ℝ) := HEq.rfl
instance evenCategoryPreadditive (C : Supercategory) : Preadditive (Even C) where
  homGroup X Y := Pi.addCommGroup
  add_comp := (Legacy.evenCategoryPreadditive (toLegacySupercategory C)).add_comp
  comp_add := (Legacy.evenCategoryPreadditive (toLegacySupercategory C)).comp_add
/-- Addition on even morphisms is inherited from the specified sVec Hom objects. -/
theorem evenCategoryPreadditive_data (C : Supercategory) (X Y : Even C) :
    (evenCategoryPreadditive C).homGroup X Y =
      Pi.addCommGroup := rfl

def grade (C : Supercategory) (X Y : TotalCategory C) (a : ZMod 2) :
    Submodule ℝ (X ⟶ Y) := Submodule.pi {a}ᶜ (fun _ => ⊥)

def SameParityOrbit (C : Supercategory) (X Y : TotalCategory C) : Prop :=
  ∃ (a : ZMod 2) (e : X ≅ Y), e.hom ∈ grade C X Y a ∧ e.inv ∈ grade C Y X a

/-! The total action is obtained componentwise from an enriched functor. -/
def tMap {C D : Supercategory} (F : Superfunctor C D)
    {X Y : C} (f : THom C X Y) : THom D (F.obj X) (F.obj Y) :=
  fun a => F.map X Y a (f a)

/-! A parity shift is an odd graded natural isomorphism, with an explicit inverse. -/
structure ParityShift (C : Supercategory) where
  functor : Superfunctor C C
  hom : GradedNatTrans ((Center.ofBraided SuperVec).obj oddLine)
    (EnrichedFunctor.id SuperVec C) functor
  inv : ∀ X, oddLine ⟶ SHom C (functor.obj X) X
  hom_inv : ∀ X, tComp C (homogeneousPoint 1 (hom.app X))
    (homogeneousPoint 1 (inv X)) = evenPoint (eId SuperVec X)
  inv_hom : ∀ X, tComp C (homogeneousPoint 1 (inv X))
    (homogeneousPoint 1 (hom.app X)) = evenPoint (eId SuperVec (functor.obj X))
structure PiSupercategory extends toSupercategory : Supercategory where
  parityShift : ParityShift toSupercategory

/-! The super tensor product tensors Hom objects and uses Koszul interchange. -/
instance superTensorProductEnriched (C D : Supercategory) :
    EnrichedCategory SuperVec (C × D) where
  Hom X Y := SHom C X.1 Y.1 ⊗ SHom D X.2 Y.2
  id X := (λ_ (𝟙_ SuperVec)).inv ≫ (eId SuperVec X.1 ⊗ₘ eId SuperVec X.2)
  comp X Y Z := tensorμ _ _ _ _ ≫
    (eComp SuperVec X.1 Y.1 Z.1 ⊗ₘ eComp SuperVec X.2 Y.2 Z.2)
  id_comp := (Legacy.superTensorProductLaws (toLegacySupercategory C) (toLegacySupercategory D)).id_comp
  comp_id := (Legacy.superTensorProductLaws (toLegacySupercategory C) (toLegacySupercategory D)).comp_id
  assoc := (Legacy.superTensorProductLaws (toLegacySupercategory C) (toLegacySupercategory D)).assoc
/-- Fix every computational field of the enriched tensor-product instance. -/
theorem superTensorProductEnriched_data (C D : Supercategory) :
    (superTensorProductEnriched C D).Hom =
      (fun X Y : C × D => SHom C X.1 Y.1 ⊗ SHom D X.2 Y.2) ∧
    HEq (superTensorProductEnriched C D).id
      (fun X : C × D => (λ_ (𝟙_ SuperVec)).inv ≫ (eId SuperVec X.1 ⊗ₘ eId SuperVec X.2)) ∧
    HEq (superTensorProductEnriched C D).comp
      (fun X Y Z : C × D => tensorμ _ _ _ _ ≫
        (eComp SuperVec X.1 Y.1 Z.1 ⊗ₘ eComp SuperVec X.2 Y.2 Z.2)) :=
  ⟨rfl, HEq.rfl, HEq.rfl⟩
abbrev SuperTensorProduct (C D : Supercategory) : Supercategory := EnrichedCat.of SuperVec (C × D)

/-! Compare the enriched tensor with the ordinary tensor on even morphisms. -/
section TensorCompatibility
variable {C : Supercategory} [monoidal : MonoidalCategory (Even C)]

/-- The enriched and ordinary tensor products have the same object operation. -/
def TensorObjectsAgree (T : Superfunctor (SuperTensorProduct C C) C) : Prop :=
  ∀ X Y : Even C, evenObj C (T.obj (X, Y)) = X ⊗ Y

/-- Transport the enriched tensor map along its specified agreement on objects. -/
def enrichedTensorMap (T : Superfunctor (SuperTensorProduct C C) C) (h : TensorObjectsAgree T)
    (X X' Y Y' : Even C) : SHom C X X' ⊗ SHom C Y Y' ⟶ SHom C (tensorObj (C := Even C) X Y) (tensorObj (C := Even C) X' Y') :=
  T.map (X, Y) (X', Y') ≫
    eqToHom (congrArg₂ (fun A B : Even C => SHom C A B) (h X Y) (h X' Y'))

def tTensor (T : Superfunctor (SuperTensorProduct C C) C) (h : TensorObjectsAgree T)
    {X X' Y Y' : Even C} (f : THom C X X') (g : THom C Y Y') :
    THom C (tensorObj (C := Even C) X Y) (tensorObj (C := Even C) X' Y') := fun a =>
  enrichedTensorMap T h X X' Y Y' a
    (∑ i : ZMod 2, GradedObject.Monoidal.ιTensorObj (SHom C X X') (SHom C Y Y')
      i (a - i) a ((add_comm i (a - i)).trans (sub_add_cancel a i)) (f i ⊗ₜ[ℝ] g (a - i)))
end TensorCompatibility

/-! Mathlib supplies even coherence; the same tensor is natural in every degree. -/
structure MonoidalSuperstructure (C : Supercategory) where
  even : MonoidalCategory (Even C)
  tensor : Superfunctor (SuperTensorProduct C C) C
  tensor_objects : letI := even; TensorObjectsAgree tensor
  tensor_even : letI := even
    ∀ {X X' Y Y' : Even C} (f : X ⟶ X') (g : Y ⟶ Y'),
      (λ_ (𝟙_ SuperVec)).inv ≫
        (ForgetEnrichment.homTo SuperVec f ⊗ₘ ForgetEnrichment.homTo SuperVec g) ≫
        enrichedTensorMap tensor tensor_objects X X' Y Y' =
          ForgetEnrichment.homTo SuperVec (f ⊗ₘ g)
  associator_naturality : letI := even
    ∀ {X X' Y Y' Z Z' : Even C} (f : THom C X X') (g : THom C Y Y') (h : THom C Z Z'),
      tComp C (tTensor tensor tensor_objects (tTensor tensor tensor_objects f g) h)
        (evenPoint (ForgetEnrichment.homTo SuperVec (α_ X' Y' Z').hom)) =
      tComp C (evenPoint (ForgetEnrichment.homTo SuperVec (α_ X Y Z).hom))
        (tTensor tensor tensor_objects f (tTensor tensor tensor_objects g h))
  left_naturality : letI := even
    ∀ {X Y : Even C} (f : THom C X Y),
      tComp C (tTensor tensor tensor_objects (evenPoint (eId (C := C) SuperVec (𝟙_ (Even C)))) f)
        (evenPoint (ForgetEnrichment.homTo SuperVec (λ_ Y).hom)) =
      tComp C (evenPoint (ForgetEnrichment.homTo SuperVec (λ_ X).hom)) f
  right_naturality : letI := even
    ∀ {X Y : Even C} (f : THom C X Y),
      tComp C (tTensor tensor tensor_objects f (evenPoint (eId (C := C) SuperVec (𝟙_ (Even C)))))
        (evenPoint (ForgetEnrichment.homTo SuperVec (ρ_ Y).hom)) =
      tComp C (evenPoint (ForgetEnrichment.homTo SuperVec (ρ_ X).hom)) f
structure MonoidalSupercategory extends toSupercategory : Supercategory where
  monoidalStructure : MonoidalSuperstructure toSupercategory
structure MonoidalPiSupercategory extends PiSupercategory where
  monoidalStructure : MonoidalSuperstructure toSupercategory

def MonoidalSupercategory.super (C : MonoidalSupercategory) : Supercategory := C.toSupercategory
def MonoidalPiSupercategory.monoidal (C : MonoidalPiSupercategory) : MonoidalSupercategory :=
  { toSupercategory := C.toSupercategory, monoidalStructure := C.monoidalStructure }

/-! The even monoidal instance is the supplied Mathlib structure, with no construction hole. -/
instance evenCategoryMonoidal (C : MonoidalSupercategory) : MonoidalCategory (Even C.super) :=
  C.monoidalStructure.even

def IsRigid (C : MonoidalSupercategory) : Prop := Nonempty (RigidCategory (Even C.super))
def IsSplitUnit (C : MonoidalSupercategory) : Prop :=
  Nonempty (CategoryTheory.End (totalObj C.super (𝟙_ (Even C.super))) ≃ₐ[ℝ] ℝ)

/-! Fusion and weak pointedness add only propositions to completed structures. -/
structure FusionPiSupercategory extends MonoidalPiSupercategory where
  rigid : IsRigid toMonoidalPiSupercategory.monoidal
  biproducts : HasFiniteBiproducts (Even toMonoidalPiSupercategory.monoidal.super)
  hom_finite : ∀ X Y a, FiniteDimensional ℝ (SHom toSupercategory X Y a)
  semisimple : letI := biproducts
    ∀ X : Even toMonoidalPiSupercategory.monoidal.super,
      ∃ (n : ℕ) (S : Fin n → Even toMonoidalPiSupercategory.monoidal.super),
        (∀ i, Simple (S i)) ∧ Nonempty (X ≅ ⨁ S)
  finite_simples : ∃ (n : ℕ) (S : Fin n → Even toMonoidalPiSupercategory.monoidal.super),
    (∀ i, Simple (S i)) ∧ ∀ X : Even toMonoidalPiSupercategory.monoidal.super, Simple X →
      ∃ i, SameParityOrbit toMonoidalPiSupercategory.monoidal.super X (S i)
  graded_schur : ∀ (X Y : Even toMonoidalPiSupercategory.monoidal.super),
    Simple X → Simple Y → ∀ a (f : THom toSupercategory X Y),
      f ∈ grade toMonoidalPiSupercategory.monoidal.super X Y a → f ≠ 0 →
        @IsIso (TotalCategory toMonoidalPiSupercategory.monoidal.super) _ X Y f
  simple_unit : Simple (𝟙_ (Even toMonoidalPiSupercategory.monoidal.super))

instance (C : FusionPiSupercategory) :
    HasFiniteBiproducts (Even C.toMonoidalPiSupercategory.monoidal.super) := C.biproducts

/-- In `ExactPairing X Y`, Y is a Mathlib right dual (an EGNO left dual). -/
def IsWeaklyInvertible (C : MonoidalPiSupercategory)
    [biproducts : HasFiniteBiproducts (Even C.monoidal.super)] (X : Even C.monoidal.super) : Prop :=
  ∃ Y : Even C.monoidal.super, Nonempty (ExactPairing X Y) ∧
    ∃ p q : ℕ, Nonempty (X ⊗ Y ≅ ⨁ (fun i : Fin p ⊕ Fin q =>
      Sum.elim (fun _ => (𝟙_ (Even C.monoidal.super)))
        (fun _ => evenObj C.monoidal.super
          (C.parityShift.functor.obj (𝟙_ (Even C.monoidal.super)))) i))
def IsWeaklyPointed (C : FusionPiSupercategory) : Prop :=
  ∀ X : Even C.toMonoidalPiSupercategory.monoidal.super,
    Simple X → IsWeaklyInvertible C.toMonoidalPiSupercategory X
/-- A fusion Pi-supercategory with real total unit endomorphisms and weakly invertible simples. -/
structure WeaklyPointedFusionPiSupercategory extends FusionPiSupercategory where
  splitUnit : IsSplitUnit toMonoidalPiSupercategory.monoidal
  weaklyPointed : IsWeaklyPointed toFusionPiSupercategory

/-! Mathlib supplies strong monoidal coherence; all-degree naturality remains explicit. -/
structure MonoidalSuperequivalence (C D : MonoidalSupercategory) where
  forward : Superfunctor C.super D.super
  backward : Superfunctor D.super C.super
  monoidal : forward.forget.CoreMonoidal
  unit : 𝟭 (Even C.super) ≅ forward.forget ⋙ backward.forget
  counit : backward.forget ⋙ forward.forget ≅ 𝟭 (Even D.super)
  unit_natural : ∀ {X Y} (f : THom C.super X Y),
    tComp C.super f (evenPoint (unit.hom.app Y)) =
      tComp C.super (evenPoint (unit.hom.app X)) (tMap backward (tMap forward f))
  counit_natural : ∀ {X Y} (f : THom D.super X Y),
    tComp D.super (tMap forward (tMap backward f)) (evenPoint (counit.hom.app Y)) =
      tComp D.super (evenPoint (counit.hom.app X)) f
  tensor_natural : ∀ {X X' Y Y'} (f : THom C.super X X') (g : THom C.super Y Y'),
    tComp D.super (tTensor (C := D.super) D.monoidalStructure.tensor D.monoidalStructure.tensor_objects
      (tMap forward f) (tMap forward g)) (evenPoint (monoidal.μIso X' Y').hom) =
    tComp D.super (evenPoint (monoidal.μIso X Y).hom)
      (tMap forward (tTensor (C := C.super) C.monoidalStructure.tensor C.monoidalStructure.tensor_objects f g))

def MonoidallySuperequivalent (C D : MonoidalSupercategory) : Prop :=
  Nonempty (MonoidalSuperequivalence C D)
instance : Coe WeaklyPointedFusionPiSupercategory MonoidalSupercategory :=
  ⟨fun C => C.toMonoidalPiSupercategory.monoidal⟩

/-! Brauer–Wall types use total endomorphism algebras of finite sums in a parity orbit. -/
def HasBrauerWallType (C : FusionPiSupercategory)
    (X : Even C.toMonoidalPiSupercategory.monoidal.super) (r : ZMod 8) : Prop :=
  let A := C.toMonoidalPiSupercategory.monoidal.super
  letI : HasFiniteBiproducts (Even A) := C.biproducts
  let Q := QuadraticMap.weightedSumSquares ℝ (fun _ : Fin r.val => (-1 : ℝ))
  ∃ (n : ℕ) (S : Fin n → Even A), 0 < n ∧
    (∀ i, SameParityOrbit A X (S i)) ∧
    ∃ e : CliffordAlgebra Q ≃ₐ[ℝ] CategoryTheory.End (totalObj A (biproduct (C := Even A) S)),
      ∀ a x, x ∈ CliffordAlgebra.evenOdd Q a ↔ e x ∈ grade A (biproduct (C := Even A) S) (biproduct (C := Even A) S) a
/-- The eight real Brauer-Wall types classify the simple parity orbits. -/
structure IsBrauerWallReference (C : WeaklyPointedFusionPiSupercategory) : Prop where
  simple_type : ∀ X : Even C.toMonoidalPiSupercategory.monoidal.super,
    Simple X → ∃! r, HasBrauerWallType C.toFusionPiSupercategory X r
  realizes_type : ∀ r, ∃ X : Even C.toMonoidalPiSupercategory.monoidal.super,
    Simple X ∧ HasBrauerWallType C.toFusionPiSupercategory X r
  type_detects_orbit : ∀ (X Y : Even C.toMonoidalPiSupercategory.monoidal.super) r,
    Simple X → Simple Y → HasBrauerWallType C.toFusionPiSupercategory X r →
    (HasBrauerWallType C.toFusionPiSupercategory Y r ↔
      SameParityOrbit C.toMonoidalPiSupercategory.monoidal.super X Y)

/-! Twists and gauges use Mathlib finite groups, homomorphisms, and units. -/
def realSign (a : ZMod 2) : ℝˣ := if a = 0 then 1 else -1

structure TwistData where
  group : FiniteGrp.{0}
  rho : group →* Multiplicative (ZMod 8)
  nu : group → group → ZMod 2
  omega : group → group → group → ℝˣ

structure TwistLaws (d : TwistData) : Prop where
  nu_one_left : ∀ g, d.nu 1 g = 0
  nu_one_right : ∀ g, d.nu g 1 = 0
  omega_one₁ : ∀ g h, d.omega 1 g h = 1
  omega_one₂ : ∀ g h, d.omega g 1 h = 1
  omega_one₃ : ∀ g h, d.omega g h 1 = 1
  cocycle : ∀ g h k,
    d.nu h k + d.nu (g * h) k + d.nu g (h * k) + d.nu g h = 0
  pentagon : ∀ g h k l,
    d.omega h k l * d.omega g (h * k) l * d.omega g h k =
      realSign (d.nu g h * d.nu k l) *
        (d.omega (g * h) k l * d.omega g h (k * l))

/-- Finite group data and normalized cochains satisfying the signed pentagon equation. -/
structure Twist where
  data : TwistData
  laws : TwistLaws data

/-! A gauge specifies a move from one source; its target cochains are computed. -/
structure GaugeData (s : TwistData) where
  targetGroup : FiniteGrp.{0}
  phi : s.group ≃* targetGroup
  lam : s.group → ZMod 2
  beta : s.group → s.group → ℝˣ
structure GaugeLaws {s : TwistData} (d : GaugeData s) : Prop where
  lam_one : d.lam 1 = 0
  beta_one_left : ∀ g, d.beta 1 g = 1
  beta_one_right : ∀ g, d.beta g 1 = 1
structure Gauge (s : TwistData) where
  data : GaugeData s
  laws : GaugeLaws data

/-- Compute the target, using the new binary cochain in the signed omega formula. -/
@[implicit_reducible] def gaugeTransformData (s : TwistData) (d : GaugeData s) : TwistData :=
  let nu g h := s.nu g h + d.lam h + d.lam (g * h) + d.lam g
  { group := d.targetGroup
    rho := s.rho.comp d.phi.symm.toMonoidHom
    nu := fun x y => nu (d.phi.symm x) (d.phi.symm y)
    omega := fun x y z =>
      let g := d.phi.symm x
      let h := d.phi.symm y
      let k := d.phi.symm z
      s.omega g h k * (d.beta (g * h) k * d.beta g h) *
        (d.beta h k * d.beta g (h * k))⁻¹ *
        realSign (nu g h * d.lam k + d.lam g * s.nu h k) }

/-- Reachability is equality with the explicitly computed target data. -/
def GaugeEquivalent (s t : TwistData) : Prop :=
  ∃ g : Gauge s, gaugeTransformData s g.data = t

end RMod.StatementLegacy
