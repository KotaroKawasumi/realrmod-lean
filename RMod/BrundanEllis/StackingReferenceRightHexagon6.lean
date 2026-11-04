import RMod.BrundanEllis.StackingReferenceHexagonCertificates6

/-! The stored intermediate matrices compose to the actual right hexagon. -/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor
theorem rightHexagon_6 (b c : ZMod 8) : RightEquation 6 b c := by
  unfold RightEquation rightLongZ
  simp only [Matrix.mul_assoc]
  rw [← right0Middle6_eq, ← right1Middle6_eq, ← right2Middle6_eq]
  exact rightFinal6 b c
end RMod.BrundanEllis.Stacking.ReferenceCommutor
