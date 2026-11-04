import RMod.Hierarchy.Bridge.LegacyReference
import RMod.Hierarchy.Bridge.WeakInvertibility
import RMod.Hierarchy.Bridge.Parameters
import RMod.Classification.Instances.TwistedPullback

/-!
# Twisted pullbacks in the enriched hierarchy

An arbitrary new reference category is passed to the proved legacy
construction through its verified presentation. Enrichment transports the
result back to the new hierarchy, retaining the specified construction data.
-/

noncomputable section
set_option autoImplicit false
namespace RMod.Legacy

private def legacyTwistedPullback (C : WeaklyPointedFusionPiSupercategory)
    (hC : IsBrauerWallReference C) (t : Twist) : Classification.PiSuperfusion.{0, 0} :=
  Classification.twistedPullback (Hierarchy.toOldPiSuperfusion C).data
    (Hierarchy.toOldReference C hC) t.toOld

def twistedPullbackData (C : WeaklyPointedFusionPiSupercategory)
    (hC : IsBrauerWallReference C) (t : Twist) : MonoidalPiSupercategoryData :=
  Hierarchy.ofOldMonoidalPiSupercategoryData (legacyTwistedPullback C hC t)

theorem twistedPullbackLaws (C : WeaklyPointedFusionPiSupercategory)
    (hC : IsBrauerWallReference C) (t : Twist) :
    MonoidalPiSupercategoryLaws (twistedPullbackData C hC t) :=
  Hierarchy.ofOldMonoidalPiSupercategoryLaws (legacyTwistedPullback C hC t)

def twistedPullback (C : WeaklyPointedFusionPiSupercategory)
    (hC : IsBrauerWallReference C) (t : Twist) : WeaklyPointedFusionPiSupercategory :=
  Hierarchy.ofOldWeaklyPointedFusionPiSupercategory (legacyTwistedPullback C hC t)

end RMod.Legacy
