import RMod.Hierarchy.Abstract.FusionPiSupercategory
import RMod.Hierarchy.Bridge.EvenMonoidalEquivalence
import RMod.Hierarchy.Bridge.ParityShiftLaws
import RMod.Hierarchy.Bridge.ParityOrbits
import RMod.Hierarchy.Bridge.SplitUnit

/-!
# Fusion structure from the old proved category

The new data contain the enriched Hom spaces, the retained monoidal
operations with the convention correction, and the specified parity
shift. Fusion conditions are transported through the even and total
equivalences; no classification statement is assumed here.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open CategoryTheory
namespace RMod.Legacy.Hierarchy
variable (P : Classification.PiSuperfusion.{0, 0})

def ofOldMonoidalPiSupercategoryData : MonoidalPiSupercategoryData where
  toPiSupercategoryData :=
    ⟨ofOldSupercategoryData P.toWeaklyPointedSuperfusion,
      ofOldParityShiftData P.toWeaklyPointedSuperfusion ⟨P.data.pi, P.laws.pi⟩⟩
  monoidal := ofOldMonoidalStructureData P.toWeaklyPointedSuperfusion

theorem ofOldMonoidalPiSupercategoryLaws :
    MonoidalPiSupercategoryLaws (ofOldMonoidalPiSupercategoryData P) where
  toPiSupercategoryLaws :=
    ⟨ofOldSupercategoryLaws P.toWeaklyPointedSuperfusion,
      ofOldParityShiftLaws P.toWeaklyPointedSuperfusion ⟨P.data.pi, P.laws.pi⟩⟩
  monoidal := ofOldMonoidalStructureLaws P.toWeaklyPointedSuperfusion

def ofOldMonoidalPiSupercategory : MonoidalPiSupercategory :=
  ⟨ofOldMonoidalPiSupercategoryData P, ofOldMonoidalPiSupercategoryLaws P⟩

def ofOldFusionPiSupercategory : FusionPiSupercategory where
  toMonoidalPiSupercategory := ofOldMonoidalPiSupercategory P
  rigid := ⟨ofOldRigidCategory P.toWeaklyPointedSuperfusion⟩
  biproducts := ofOldEvenFiniteBiproducts P.toWeaklyPointedSuperfusion
  hom_finite := ofOldHomFinite P.toWeaklyPointedSuperfusion
  semisimple := ofOldSemisimple P.toWeaklyPointedSuperfusion
  finite_simples := ofOldFiniteSimples P.toWeaklyPointedSuperfusion
  graded_schur := ofOldGradedSchur P.toWeaklyPointedSuperfusion
  simple_unit := (oldSimple_iff P.toWeaklyPointedSuperfusion P.data.tensorUnit).mp P.laws.simple_unit

theorem ofOldFusionSplitUnit : IsSplitUnit (ofOldMonoidalPiSupercategory P).monoidal :=
  ⟨ofOldUnitEndEquiv P.toWeaklyPointedSuperfusion⟩

end RMod.Legacy.Hierarchy
