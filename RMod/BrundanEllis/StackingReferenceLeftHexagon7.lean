import RMod.BrundanEllis.StackingReferenceHexagonCertificates7

/-! The stored intermediate matrices compose to the actual left hexagon. -/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor
theorem leftHexagon_7 (b c : ZMod 8) : LeftEquation 7 b c := by
  unfold LeftEquation leftShortZ leftLongZ
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← left0Middle7_eq, ← left1Middle7_eq]
  exact leftFinal7 b c
end RMod.BrundanEllis.Stacking.ReferenceCommutor
