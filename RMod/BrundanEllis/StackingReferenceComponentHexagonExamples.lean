import RMod.BrundanEllis.StackingReferenceComponentHexagon
import RMod.BrundanEllis.StackingReferenceHexagonExamples

/-! Shifted examples of the full reference component hexagons, with their
finite coefficient hypotheses discharged by ordinary kernel proofs. -/
noncomputable section
set_option autoImplicit false
namespace RMod.BrundanEllis.Stacking
open Superfusion.RMod.FromRawDCT

/-- Odd summand shifts are covered by the first component hexagon. -/
example :
    (referenceLeftHexagonShort 1 4 4 (Obj.singleton (1, 1)) (Obj.singleton (4, 1))
      (Obj.singleton (4, 0)) (referenceSingleton_component 1 1)
      (referenceSingleton_component 4 1) (referenceSingleton_component 4 0)).hom =
    (referenceLeftHexagonLong 1 4 4 (Obj.singleton (1, 1)) (Obj.singleton (4, 1))
      (Obj.singleton (4, 0)) (referenceSingleton_component 1 1)
      (referenceSingleton_component 4 1) (referenceSingleton_component 4 0)).hom :=
  referenceLeftHexagon 1 4 4 ReferenceCommutor.leftHexagon_144 _ _ _ _ _ _

/-- The nontrivial second hexagon sign survives all three odd summand shifts. -/
example :
    (referenceRightHexagonShort 1 1 1 (Obj.singleton (1, 1)) (Obj.singleton (1, 1))
      (Obj.singleton (1, 1)) (referenceSingleton_component 1 1)
      (referenceSingleton_component 1 1) (referenceSingleton_component 1 1)).hom =
    reference.data.smul (-1)
      (referenceRightHexagonLong 1 1 1 (Obj.singleton (1, 1)) (Obj.singleton (1, 1))
        (Obj.singleton (1, 1)) (referenceSingleton_component 1 1)
        (referenceSingleton_component 1 1) (referenceSingleton_component 1 1)).hom := by
  have h := referenceRightHexagon 1 1 1 ReferenceCommutor.rightHexagon_111
    (Obj.singleton (1, 1)) (Obj.singleton (1, 1)) (Obj.singleton (1, 1))
    (referenceSingleton_component 1 1) (referenceSingleton_component 1 1)
    (referenceSingleton_component 1 1)
  exact h

end RMod.BrundanEllis.Stacking
