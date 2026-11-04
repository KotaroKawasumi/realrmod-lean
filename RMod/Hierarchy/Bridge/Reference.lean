import RMod.Hierarchy.Bridge.WeakInvertibility
import RMod.Hierarchy.Bridge.BrauerWallTypes

/-!
# Transport of the Brauer-Wall reference property

The three clauses use the same simple objects and parity orbits. The
finite-sum type comparison supplies existence, uniqueness, and detection
without an additional classification assumption.
-/

noncomputable section
set_option autoImplicit false
open CategoryTheory
namespace RMod.Legacy.Hierarchy

theorem ofOldReference (P : Classification.PiSuperfusion.{0, 0})
    (hP : Classification.ReferenceProperty P.data) :
    IsBrauerWallReference (ofOldWeaklyPointedFusionPiSupercategory P) where
  simple_type X hX := by
    obtain ⟨r, hr, hu⟩ := hP.simple_type X
      ((oldSimple_iff P.toWeaklyPointedSuperfusion X).mpr hX)
    exact ⟨r, (oldBrauerWallType_iff P X r).mp hr,
      fun s hs => hu s ((oldBrauerWallType_iff P X s).mpr hs)⟩
  realizes_type r := by
    obtain ⟨X, hX, hr⟩ := hP.realizes_type r
    exact ⟨evenObj (ofOldSupercategory P.toWeaklyPointedSuperfusion) X,
      (oldSimple_iff P.toWeaklyPointedSuperfusion X).mp hX, (oldBrauerWallType_iff P X r).mp hr⟩
  type_detects_orbit X Y r hX hY hr := by
    exact (oldBrauerWallType_iff P Y r).symm.trans
      ((hP.type_detects_orbit X Y r
        ((oldSimple_iff P.toWeaklyPointedSuperfusion X).mpr hX)
        ((oldSimple_iff P.toWeaklyPointedSuperfusion Y).mpr hY)
        ((oldBrauerWallType_iff P X r).mpr hr)).trans
          (oldParityOrbit_iff P.toWeaklyPointedSuperfusion X Y))

end RMod.Legacy.Hierarchy
