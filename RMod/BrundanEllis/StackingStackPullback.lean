import RMod.BrundanEllis.StackingStackPullbackComparison
import RMod.BrundanEllis.StackingReferenceHexagon

/-! The diagonal additive parity completion realizes the closed stacking formula. -/
set_option autoImplicit false
namespace RMod.BrundanEllis

/-- Stack the two pullbacks using the prescribed twist cochains. -/
theorem stack_pullback {G : FiniteGrp.{0}} (s t : TwistOn G) :
    MonoidallySuperequivalent (stack s.val t.val (s.property.trans t.property.symm))
      (pullback (twistMul s t).val) :=
  Stacking.stack_pullback_of_reference_hexagons s t
    Stacking.ReferenceCommutor.leftHexagon_equation
    Stacking.ReferenceCommutor.rightHexagon_equation

end RMod.BrundanEllis
