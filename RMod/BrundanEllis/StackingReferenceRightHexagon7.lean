import RMod.BrundanEllis.StackingReferenceHexagonCertificates7

/-! The stored intermediate matrices compose to the actual right hexagon. -/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor
theorem rightHexagon_7 (b c : ZMod 8) : RightEquation 7 b c := by
  unfold RightEquation rightLongZ
  simp only [Matrix.mul_assoc]
  rw [← right0Middle7_eq, ← right1Middle7_eq, ← right2Middle7_eq]
  exact rightFinal7 b c
end RMod.BrundanEllis.Stacking.ReferenceCommutor
