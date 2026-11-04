import RMod.BrundanEllis.StackingReferenceHexagonMiddle1

/-! Each candidate multiplication is independently checked by the ordinary Lean kernel. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor
open Superfusion

theorem left0Middle1_eq (b c : ZMod 8) : left0Middle1 b c = outerRightZ 1 b c * associatorZ 1 b c := by
  fin_cases b <;> fin_cases c <;> decide +kernel

theorem left1Middle1_eq (b c : ZMod 8) : left1Middle1 b c = associatorZ b 1 c * innerLeftZ 1 b c := by
  fin_cases b <;> fin_cases c <;> decide +kernel

theorem right0Middle1_eq (b c : ZMod 8) : right0Middle1 b c = innerRightZ 1 b c * associatorZ 1 b c := by
  fin_cases b <;> fin_cases c <;> decide +kernel

theorem right1Middle1_eq (b c : ZMod 8) : right1Middle1 b c = associatorInverseZ 1 c b * right0Middle1 b c := by
  fin_cases b <;> fin_cases c <;> decide +kernel

theorem right2Middle1_eq (b c : ZMod 8) : right2Middle1 b c = innerLeftZ 1 c b * right1Middle1 b c := by
  fin_cases b <;> fin_cases c <;> decide +kernel

theorem leftFinal1 (b c : ZMod 8) :
    ((-1 : ℤ) ^ (leftScaleBit 1 b c).val * positiveScale (leftScaleExponent 1 b c)) •
      (associatorZ b c 1 * left0Middle1 b c) =
    negativeScale (leftScaleExponent 1 b c) • (innerRightZ b 1 c * left1Middle1 b c) := by
  fin_cases b <;> fin_cases c <;> decide +kernel

theorem rightFinal1 (b c : ZMod 8) :
    ((-1 : ℤ) ^ (rightScaleBit 1 b c).val * positiveScale (rightScaleExponent 1 b c) *
      (RMod.ConstructiveConnectorTable.inverseScale 1 c b : ℤ)) • outerLeftZ 1 b c =
    negativeScale (rightScaleExponent 1 b c) • (associatorZ c 1 b * right2Middle1 b c) := by
  fin_cases b <;> fin_cases c <;> decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor
