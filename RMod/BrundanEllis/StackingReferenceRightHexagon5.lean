import RMod.BrundanEllis.StackingReferenceHexagonCertificates5

/-! The stored intermediate matrices compose to the actual right hexagon. -/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor
theorem rightHexagon_5 (b c : ZMod 8) : RightEquation 5 b c := by
  unfold RightEquation rightLongZ
  simp only [Matrix.mul_assoc]
  rw [← right0Middle5_eq, ← right1Middle5_eq, ← right2Middle5_eq]
  exact rightFinal5 b c
end RMod.BrundanEllis.Stacking.ReferenceCommutor
