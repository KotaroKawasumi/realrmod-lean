import RMod.Hierarchy.Bridge.Reference
import RMod.Classification.Proofs.RealReference

/-!
# The real model in the new hierarchy

The existing real regular-module construction and its proved reference
property are reused through the verified adapters. No mathematical
construction or classification proof is replaced by a new assumption.
-/

noncomputable section
set_option autoImplicit false
namespace RMod.Legacy

def realFusionPiSupercategoryData : MonoidalPiSupercategoryData :=
  Hierarchy.ofOldMonoidalPiSupercategoryData Classification.realPiSuperfusion

theorem realFusionPiSupercategoryLaws :
    MonoidalPiSupercategoryLaws realFusionPiSupercategoryData :=
  Hierarchy.ofOldMonoidalPiSupercategoryLaws Classification.realPiSuperfusion

def realFusionPiSupercategory : WeaklyPointedFusionPiSupercategory :=
  Hierarchy.ofOldWeaklyPointedFusionPiSupercategory Classification.realPiSuperfusion

theorem real_isBrauerWallReference : IsBrauerWallReference realFusionPiSupercategory :=
  Hierarchy.ofOldReference Classification.realPiSuperfusion Classification.realReference

end RMod.Legacy
