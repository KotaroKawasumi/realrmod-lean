import RMod.BrundanEllis.StackingReferenceHexagonCertificates2

/-! The stored intermediate matrices compose to the actual right hexagon. -/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor
theorem rightHexagon_2 (b c : ZMod 8) : RightEquation 2 b c := by
  unfold RightEquation rightLongZ
  simp only [Matrix.mul_assoc]
  rw [← right0Middle2_eq, ← right1Middle2_eq, ← right2Middle2_eq]
  exact rightFinal2 b c
end RMod.BrundanEllis.Stacking.ReferenceCommutor
