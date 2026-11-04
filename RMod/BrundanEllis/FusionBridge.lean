import RMod.BrundanEllis.ParityBridge
import RMod.BrundanEllis.DualDecomposition
import RMod.Enriched.Classification

/-! Transport the unchanged fusion and real-reference conditions.
The chosen right dual and two finite sums give the earlier existential pairing
condition. The ordinary right unitor then identifies pi and pi tensor the unit. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace RMod.BrundanEllis.Bridge

/-- The chosen-dual presentation is equivalent to an intrinsic existential pairing. -/
theorem weaklyInvertible_pairing_iff (C : Type) [SuperCategory C]
    [MonoidalCategory (Even C)] [MonoidalPiSuperCategory C]
    [RigidCategory (Even C)] [HasFiniteBiproducts (Even C)] (X : Even C) :
    IsWeaklyInvertible C X ↔
      ∃ Y : Even C, Nonempty (ExactPairing X Y) ∧
        ∃ p q : ℕ, Nonempty (X ⊗ Y ≅ ⨁ Sum.elim
          (fun _ : Fin p => 𝟙_ (Even C))
          (fun _ : Fin q => evenObj C (MonoidalPiSuperCategory.pi (C := C)))) :=
  MathlibBridge.chosenRightDualDecomposition_iff X
    (evenObj C (MonoidalPiSuperCategory.pi (C := C)))

/-- The right unitor identifies the two weak-invertibility conditions in both directions. -/
theorem weaklyInvertible_iff (C : Type) [SuperCategory C]
    [MonoidalCategory (Even C)] [MonoidalSuperCategory C] [MonoidalPiSuperCategory C]
    [RigidCategory (Even C)] [HasFiniteBiproducts (Even C)] (X : Even C) :
    letI : RMod.PiSuperCategory C := ⟨ParityConstruction.parityShift C⟩
    IsWeaklyInvertible C X ↔ RMod.IsWeaklyInvertible C X := by
  rw [weaklyInvertible_pairing_iff]
  constructor
  · rintro ⟨Y, hY, p, q, ⟨e⟩⟩
    refine ⟨Y, hY, p, q, ⟨e ≪≫ ?_⟩⟩
    apply biproduct.mapIso
    intro i
    cases i with
    | inl j => exact Iso.refl _
    | inr j => exact (ρ_ (evenObj C (MonoidalPiSuperCategory.pi (C := C)))).symm
  · rintro ⟨Y, hY, p, q, ⟨e⟩⟩
    refine ⟨Y, hY, p, q, ⟨e ≪≫ ?_⟩⟩
    apply biproduct.mapIso
    intro i
    cases i with
    | inl j => exact Iso.refl _
    | inr j => exact ρ_ (evenObj C (MonoidalPiSuperCategory.pi (C := C)))

/-- Existing models provide the specified parity object by evaluation at the unit. -/
def fromStage (C : RMod.WeaklyPointedFusionPiSuperCat) : WeaklyPointedFusionPiSuperCat := by
  letI : SuperCategory C := C.superCategory
  letI : MonoidalCategory (Even C) := C.monoidalCategory
  letI : RMod.MonoidalEnrichedCategory SuperVec C := C.monoidalEnrichedCategory
  letI : RigidCategory (Even C) := C.rigidCategory
  letI : Abelian (Even C) := C.abelian
  letI : MonoidalPiSuperCategory C := piObjectOfShift C
  letI : MonoidalSuperCategory C := fromEnriched C
  letI : FusionPiSuperCategory C := {
    hom_finite := C.fusion.hom_finite
    semisimple := C.fusion.semisimple
    finite_simples := C.fusion.finite_simples
    simple_unit := C.fusion.simple_unit }
  letI : WeaklyPointedFusionPiSuperCategory C := {
    splitUnit := C.weaklyPointed.splitUnit
    weaklyPointed := by
      intro X hX
      exact (weaklyInvertible_pairing_iff C X).mpr
        (C.weaklyPointed.weaklyPointed X hX) }
  exact {
    carrier := C
    superCategory := C.superCategory
    monoidalCategory := C.monoidalCategory
    piSuperCategory := inferInstance
    monoidalSuperCategory := inferInstance
    rigidCategory := C.rigidCategory
    abelian := C.abelian
    fusion := inferInstance
    weaklyPointed := inferInstance }

/-- Arbitrary new inputs supply the earlier parity-shift-based classification input. -/
def toStage (C : WeaklyPointedFusionPiSuperCat) : RMod.WeaklyPointedFusionPiSuperCat := by
  letI : RMod.SuperCategory C := C.superCategory
  letI : MonoidalCategory (RMod.Even C) := C.monoidalCategory
  letI : RigidCategory (RMod.Even C) := C.rigidCategory
  letI : Abelian (RMod.Even C) := C.abelian
  letI : RMod.PiSuperCategory C := ⟨ParityConstruction.parityShift C⟩
  letI : RMod.MonoidalEnrichedCategory SuperVec C := toEnriched C
  letI : RMod.FusionPiSuperCategory C := {
    hom_finite := C.fusion.hom_finite
    semisimple := C.fusion.semisimple
    finite_simples := C.fusion.finite_simples
    simple_unit := C.fusion.simple_unit }
  letI : RMod.WeaklyPointedFusionPiSuperCategory C := {
    splitUnit := C.weaklyPointed.splitUnit
    weaklyPointed := by
      intro X hX
      exact (weaklyInvertible_iff C X).mp
        (C.weaklyPointed.weaklyPointed X hX) }
  exact {
    carrier := C
    superCategory := C.superCategory
    piSuperCategory := inferInstance
    monoidalCategory := C.monoidalCategory
    monoidalEnrichedCategory := inferInstance
    rigidCategory := C.rigidCategory
    abelian := C.abelian
    fusion := inferInstance
    weaklyPointed := inferInstance }

/-- All total endomorphism algebras and their grading retain the same operations. -/
def toReference (C : WeaklyPointedFusionPiSuperCat) (h : IsBrauerWallReference C) :
    RMod.IsBrauerWallReference (toStage C) where
  simple_type := h.simple_type
  realizes_type := h.realizes_type
  type_detects_orbit := h.type_detects_orbit

def fromReference (C : RMod.WeaklyPointedFusionPiSuperCat)
    (h : RMod.IsBrauerWallReference C) : IsBrauerWallReference (fromStage C) where
  simple_type := h.simple_type
  realizes_type := h.realizes_type
  type_detects_orbit := h.type_detects_orbit

/-- The enriched equivalence of the earlier implementation supplies the public comparisons. -/
theorem fromStageEquivalence (C D : WeaklyPointedFusionPiSuperCat)
    (e : RMod.MonoidallySuperequivalent (toStage C) (toStage D)) :
    MonoidallySuperequivalent C D := by
  rcases e with ⟨e⟩
  exact ⟨fromStatementEquivalence C D (RMod.EnrichedBridge.toEquivalence _ _ e)⟩

/-- Public comparisons give a strong enriched equivalence for the earlier implementation. -/
theorem toStageEquivalence (C D : WeaklyPointedFusionPiSuperCat)
    (e : MonoidallySuperequivalent C D) :
    RMod.MonoidallySuperequivalent (toStage C) (toStage D) := by
  rcases e with ⟨e⟩
  exact ⟨RMod.EnrichedBridge.fromEquivalence _ _ (toStatementEquivalence C D e)⟩

/-- A model imported from the earlier implementation retains its monoidal structure. -/
theorem importedEquivalence (C D : RMod.WeaklyPointedFusionPiSuperCat)
    (e : RMod.MonoidallySuperequivalent C D) :
    MonoidallySuperequivalent (fromStage C) (fromStage D) := by
  rcases e with ⟨e⟩
  exact ⟨fromStatementEquivalence (fromStage C) (fromStage D)
    (RMod.EnrichedBridge.toEquivalence C D e)⟩

end RMod.BrundanEllis.Bridge
