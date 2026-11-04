import RMod.Enriched.FusionBridge
import RMod.Enriched.EquivalenceNaturality

/-! Ordinary unit and counit components and the strong tensorator are retained;
total naturality supplies their full enriched naturality. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace RMod.EnrichedBridge

variable (C D : StatementLegacy.MonoidalSupercategory)
local instance : MonoidalCategory (Even (C.super : Type)) := C.monoidalStructure.even
local instance : MonoidalCategory (Even (D.super : Type)) := D.monoidalStructure.even
local instance : MonoidalEnrichedCategory SuperVec (C.super : Type) := fromMonoidal C
local instance : MonoidalEnrichedCategory SuperVec (D.super : Type) := fromMonoidal D

/-- The old equivalence data define a genuine enriched monoidal equivalence. -/
def fromEquivalence (e : StatementLegacy.MonoidalSuperequivalence C D) :
    MonoidalEnrichedEquivalence SuperVec (C.super : Type) (D.super : Type) where
  functor := e.forward
  inverse := e.backward
  unitIso := EnrichedSupport.natIsoOfTotal _ _ e.unit (fun f => e.unit_natural f)
  counitIso := EnrichedSupport.natIsoOfTotal _ _ e.counit (fun f => e.counit_natural f)
  monoidal := EnrichedSupport.monoidalOfTotal e.forward e.monoidal e.tensor_natural

end RMod.EnrichedBridge
