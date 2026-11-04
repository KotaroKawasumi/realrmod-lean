import RMod.BrundanEllis.StackingModelBridge
import RMod.Enriched.TotalNaturality
import RMod.Hierarchy.Bridge.OldEvenValues

/-! Even pre- and postcomposition on the public pullback Hom spaces are
coordinatewise composition in the reference category. These formulas let
homogeneous coordinate calculations prove enriched naturality equations. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open CategoryTheory
namespace RMod.BrundanEllis.Stacking
open RMod.Classification

/-- Read the actual coordinate map of an even pullback morphism. -/
def pullbackEvenValue (s : Twist) {X Y : Even (pullback s)} (f : X ⟶ Y) :
    PullbackHom reference.data (oldTwist s).data X Y :=
  (RMod.Legacy.Hierarchy.evenHomEquiv (oldPullback s).toWeaklyPointedSuperfusion X Y f).hom

/-- Postcomposition by an even map has no extra Koszul sign. -/
theorem pullback_post_apply (s : Twist) {X Y Z : Even (pullback s)}
    (a : ZMod 2) (f : SHom (pullback s) X Y a) (q : Y ⟶ Z) (g : s.group) :
    (eHomWhiskerLeft SuperVec X q a f).val g =
      reference.data.comp (f.val g) (pullbackEvenValue s q g) := by
  letI : RMod.SuperCategory (pullback s) := inferInstanceAs (SuperCategory (pullback s))
  have hp := RMod.Regression.post_apply (pullback s) (Pi.single a f) q a
  rw [RMod.Regression.comp_even_right] at hp
  simp only [Pi.single_eq_same] at hp
  erw [hp]
  have he := RMod.Legacy.Hierarchy.oldEnrichedComp_tmul (oldPullback s).toWeaklyPointedSuperfusion X Y Z
    a 0 a (add_zero a) f
    (RMod.evenPoint (ForgetEnrichment.homTo SuperVec q) 0)
  exact congrFun he g

/-- Precomposition by an even map is the other coordinatewise composite. -/
theorem pullback_pre_apply (s : Twist) {X Y Z : Even (pullback s)}
    (a : ZMod 2) (f : X ⟶ Y) (q : SHom (pullback s) Y Z a) (g : s.group) :
    (eHomWhiskerRight SuperVec f Z a q).val g =
      reference.data.comp (pullbackEvenValue s f g) (q.val g) := by
  letI : RMod.SuperCategory (pullback s) := inferInstanceAs (SuperCategory (pullback s))
  have hp := RMod.Regression.pre_apply (pullback s) f (Pi.single a q) a
  rw [RMod.Regression.comp_even_left] at hp
  simp only [Pi.single_eq_same] at hp
  erw [hp]
  have he := RMod.Legacy.Hierarchy.oldEnrichedComp_tmul (oldPullback s).toWeaklyPointedSuperfusion X Y Z
    0 a a (zero_add a)
    (RMod.evenPoint (ForgetEnrichment.homTo SuperVec f) 0) q
  exact congrFun he g

end RMod.BrundanEllis.Stacking
