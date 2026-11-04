import RMod.BrundanEllis.StackingReferenceHexagonCertificates0

/-! The stored intermediate matrices compose to the actual left hexagon. -/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor
theorem leftHexagon_0 (b c : ZMod 8) : LeftEquation 0 b c := by
  unfold LeftEquation leftShortZ leftLongZ
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← left0Middle0_eq, ← left1Middle0_eq]
  exact leftFinal0 b c
end RMod.BrundanEllis.Stacking.ReferenceCommutor
