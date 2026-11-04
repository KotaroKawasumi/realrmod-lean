import RMod.BrundanEllis.StackingReferenceHexagonNormalization

/-! Nontrivial closed checks of the reference hexagon coefficients.
These three faces are examples, not a substitute for the all-label theorem. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor

/-- A unit face with a nontrivial normalization scalar. -/
theorem leftHexagon_104 : LeftEquation 1 0 4 := by
  unfold LeftEquation
  decide +kernel

/-- A second face in the order-two degree-four cycle. -/
theorem leftHexagon_144 : LeftEquation 1 4 4 := by
  unfold LeftEquation
  decide +kernel

/-- The quadratic sign defect is nonzero on this triple. -/
theorem rightHexagon_111 : RightEquation 1 1 1 := by
  unfold RightEquation
  decide +kernel

example : rightDefect 1 1 1 = 1 := rfl
example : normalizationExponent 1 1 = -1 := rfl

end RMod.BrundanEllis.Stacking.ReferenceCommutor
