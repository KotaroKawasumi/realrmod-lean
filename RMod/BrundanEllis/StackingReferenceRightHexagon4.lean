import RMod.BrundanEllis.StackingReferenceHexagonCertificates4

/-! The stored intermediate matrices compose to the actual right hexagon. -/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor
theorem rightHexagon_4 (b c : ZMod 8) : RightEquation 4 b c := by
  unfold RightEquation rightLongZ
  simp only [Matrix.mul_assoc]
  rw [← right0Middle4_eq, ← right1Middle4_eq, ← right2Middle4_eq]
  exact rightFinal4 b c
end RMod.BrundanEllis.Stacking.ReferenceCommutor
