import RMod.BrundanEllis.StackingReferenceHexagonMiddle0

/-! Each candidate multiplication is independently checked by the ordinary Lean kernel. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor
open Superfusion

theorem left0Middle0_eq (b c : ZMod 8) : left0Middle0 b c = outerRightZ 0 b c * associatorZ 0 b c := by
  fin_cases b <;> fin_cases c <;> decide +kernel

theorem left1Middle0_eq (b c : ZMod 8) : left1Middle0 b c = associatorZ b 0 c * innerLeftZ 0 b c := by
  fin_cases b <;> fin_cases c <;> decide +kernel

theorem right0Middle0_eq (b c : ZMod 8) : right0Middle0 b c = innerRightZ 0 b c * associatorZ 0 b c := by
  fin_cases b <;> fin_cases c <;> decide +kernel

theorem right1Middle0_eq (b c : ZMod 8) : right1Middle0 b c = associatorInverseZ 0 c b * right0Middle0 b c := by
  fin_cases b <;> fin_cases c <;> decide +kernel

theorem right2Middle0_eq (b c : ZMod 8) : right2Middle0 b c = innerLeftZ 0 c b * right1Middle0 b c := by
  fin_cases b <;> fin_cases c <;> decide +kernel

theorem leftFinal0 (b c : ZMod 8) :
    ((-1 : ℤ) ^ (leftScaleBit 0 b c).val * positiveScale (leftScaleExponent 0 b c)) •
      (associatorZ b c 0 * left0Middle0 b c) =
    negativeScale (leftScaleExponent 0 b c) • (innerRightZ b 0 c * left1Middle0 b c) := by
  fin_cases b <;> fin_cases c <;> decide +kernel

theorem rightFinal0 (b c : ZMod 8) :
    ((-1 : ℤ) ^ (rightScaleBit 0 b c).val * positiveScale (rightScaleExponent 0 b c) *
      (RMod.ConstructiveConnectorTable.inverseScale 0 c b : ℤ)) • outerLeftZ 0 b c =
    negativeScale (rightScaleExponent 0 b c) • (associatorZ c 0 b * right2Middle0 b c) := by
  fin_cases b <;> fin_cases c <;> decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor
