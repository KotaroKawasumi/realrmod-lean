import RMod.Enriched.TotalNaturality
import RMod.Statement.Classification

/-! The carrier-based enriched interface supplies every operation and all-degree
naturality law required by the established bundled classification interface. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace RMod.EnrichedBridge

/-- Rebundle the same small carrier and enrichment, without choosing new operations. -/
@[implicit_reducible] def bundled (C : Type) [SuperCategory C] : StatementLegacy.Supercategory :=
  EnrichedCat.of SuperVec C

/-- The odd parity transformation and its inverse have unchanged components. -/
def toParityShift (C : Type) [SuperCategory C] [PiSuperCategory C] :
    StatementLegacy.ParityShift (bundled C) where
  functor := (PiSuperCategory.parityShift (C := C)).functor
  hom := (PiSuperCategory.parityShift (C := C)).hom
  inv := (PiSuperCategory.parityShift (C := C)).inv
  hom_inv := (PiSuperCategory.parityShift (C := C)).hom_inv
  inv_hom := (PiSuperCategory.parityShift (C := C)).inv_hom

/-- The existing ordinary tensor and enriched tensor provide the previous monoidal interface. -/
def toMonoidal (C : Type) [SuperCategory C]
    [mc : MonoidalCategory (Even C)] [M : MonoidalEnrichedCategory SuperVec C] :
    StatementLegacy.MonoidalSupercategory where
  toSupercategory := bundled C
  monoidalStructure := {
    even := mc
    tensor := M.tensor
    tensor_objects := M.tensor_objects
    tensor_even := M.tensor_even
    associator_naturality := Regression.associator_natural (C := C)
    left_naturality := Regression.leftUnitor_natural (C := C)
    right_naturality := Regression.rightUnitor_natural (C := C) }

/-- Bundle parity with the same monoidal structure. -/
def toPiMonoidal (C : Type) [SuperCategory C] [PiSuperCategory C]
    [MonoidalCategory (Even C)] [MonoidalEnrichedCategory SuperVec C] :
    StatementLegacy.MonoidalPiSupercategory where
  toSupercategory := bundled C
  parityShift := toParityShift C
  monoidalStructure := (toMonoidal C).monoidalStructure

/-- The new enriched equivalence retains full total-morphism naturality. -/
def toEquivalence (C D : Type) [SuperCategory C] [SuperCategory D]
    [MonoidalCategory (Even C)] [MonoidalCategory (Even D)]
    [MonoidalEnrichedCategory SuperVec C] [MonoidalEnrichedCategory SuperVec D]
    (e : MonoidalEnrichedEquivalence SuperVec C D) :
    StatementLegacy.MonoidalSuperequivalence (toMonoidal C) (toMonoidal D) where
  forward := e.functor
  backward := e.inverse
  monoidal := e.monoidal.coreMonoidal
  unit := e.unitIso.toNatIso
  counit := e.counitIso.toNatIso
  unit_natural := Regression.unit_natural e
  counit_natural := Regression.counit_natural e
  tensor_natural := Regression.tensor_natural e.monoidal

end RMod.EnrichedBridge
