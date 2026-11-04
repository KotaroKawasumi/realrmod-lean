import RMod.BrundanEllis.StackingOrbitTensor
import RMod.Hierarchy.Bridge.LegacyReference
import RMod.Classification.Instances.SimpleOrbitGroup

/-! Retain the existing intrinsic finite group of simple parity orbits for
an arbitrary input category. These adapters do not introduce a marking or
change the objects, tensor operations, or parity relation. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace RMod.BrundanEllis.Stacking
variable (C : WeaklyPointedFusionPiSuperCat)

def intrinsicLegacy : RMod.Legacy.WeaklyPointedFusionPiSupercategory :=
  RMod.StatementLegacy.StatementBridge.toWeak
    (RMod.EnrichedBridge.toWeak (Bridge.toStage C))

def intrinsicOld : RMod.Classification.PiSuperfusion.{0, 0} :=
  RMod.Legacy.Hierarchy.toOldPiSuperfusion (intrinsicLegacy C)

/-- The raw simple predicate is the same even categorical simplicity. -/
theorem intrinsic_simple (X : C) :
    (intrinsicOld C).data.IsSimple X ↔ Simple (evenObj C X) := by
  with_unfolding_all
    exact RMod.Legacy.Hierarchy.legacySimple_iff
      (intrinsicLegacy C).toMonoidalPiSupercategory.monoidal X

/-- The quotient relation remains the specified all-degree parity orbit. -/
theorem intrinsic_orbit (X Y : C) :
    RMod.Classification.SameParityOrbit
      (intrinsicOld C).data.toWeaklyPointedSuperfusionData X Y ↔
      SameParityOrbit C X Y := by
  with_unfolding_all
    exact (RMod.Legacy.Hierarchy.legacyParityOrbit_iff (intrinsicLegacy C) X Y).trans
      (RMod.StatementLegacy.StatementBridge.orbit_toSuper (Bridge.bundled C) X Y)

/-- Even finite decompositions use the existing Mathlib biproducts. -/
theorem intrinsic_decomposition (X : C) {n : ℕ} (S : Fin n → C) :
    (intrinsicOld C).data.HasDecomposition X S ↔
      Nonempty (evenObj C X ≅ ⨁ (fun i => evenObj C (S i))) := by
  with_unfolding_all
    exact RMod.Legacy.Hierarchy.legacyDecomposition_iff (intrinsicLegacy C) X S

/-- This is the existing group of actual simple classes, rather than type labels. -/
def intrinsicOrbitGroup : FiniteGrp :=
  RMod.Classification.simpleOrbitFiniteGroup (intrinsicOld C).toWeaklyPointedSuperfusion

end RMod.BrundanEllis.Stacking
