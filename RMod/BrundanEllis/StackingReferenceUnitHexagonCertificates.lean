import RMod.BrundanEllis.StackingReferenceHexagonData

/-! The small unit cases of both coefficient hexagons, verified in the
ordinary Lean kernel independently of the full three-label certificates. -/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor

/-- The unit case required for exchanging an arbitrary component with the unit. -/
theorem leftHexagon_unit (a : ZMod 8) : LeftEquation a 0 0 := by
  unfold LeftEquation
  fin_cases a <;> decide +kernel

/-- The unit case required for exchanging the unit with an arbitrary component. -/
theorem rightHexagon_unit (a : ZMod 8) : RightEquation 0 0 a := by
  unfold RightEquation
  fin_cases a <;> decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor
