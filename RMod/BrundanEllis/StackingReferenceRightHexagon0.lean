import RMod.BrundanEllis.StackingReferenceHexagonCertificates0

/-! The stored intermediate matrices compose to the actual right hexagon. -/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor
theorem rightHexagon_0 (b c : ZMod 8) : RightEquation 0 b c := by
  unfold RightEquation rightLongZ
  simp only [Matrix.mul_assoc]
  rw [← right0Middle0_eq, ← right1Middle0_eq, ← right2Middle0_eq]
  exact rightFinal0 b c
end RMod.BrundanEllis.Stacking.ReferenceCommutor
