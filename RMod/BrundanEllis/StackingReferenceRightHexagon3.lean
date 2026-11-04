import RMod.BrundanEllis.StackingReferenceHexagonCertificates3

/-! The stored intermediate matrices compose to the actual right hexagon. -/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor
theorem rightHexagon_3 (b c : ZMod 8) : RightEquation 3 b c := by
  unfold RightEquation rightLongZ
  simp only [Matrix.mul_assoc]
  rw [← right0Middle3_eq, ← right1Middle3_eq, ← right2Middle3_eq]
  exact rightFinal3 b c
end RMod.BrundanEllis.Stacking.ReferenceCommutor
