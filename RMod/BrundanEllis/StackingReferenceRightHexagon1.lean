import RMod.BrundanEllis.StackingReferenceHexagonCertificates1

/-! The stored intermediate matrices compose to the actual right hexagon. -/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor
theorem rightHexagon_1 (b c : ZMod 8) : RightEquation 1 b c := by
  unfold RightEquation rightLongZ
  simp only [Matrix.mul_assoc]
  rw [← right0Middle1_eq, ← right1Middle1_eq, ← right2Middle1_eq]
  exact rightFinal1 b c
end RMod.BrundanEllis.Stacking.ReferenceCommutor
