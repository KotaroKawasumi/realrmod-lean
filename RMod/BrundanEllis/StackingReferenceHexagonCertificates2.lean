import RMod.BrundanEllis.StackingReferenceHexagonMiddle2

/-! Each candidate multiplication is independently checked by the ordinary Lean kernel. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor
open Superfusion

theorem left0Middle2_eq (b c : ZMod 8) : left0Middle2 b c = outerRightZ 2 b c * associatorZ 2 b c := by
  fin_cases b <;> fin_cases c <;> decide +kernel

theorem left1Middle2_eq (b c : ZMod 8) : left1Middle2 b c = associatorZ b 2 c * innerLeftZ 2 b c := by
  fin_cases b <;> fin_cases c <;> decide +kernel

theorem right0Middle2_eq (b c : ZMod 8) : right0Middle2 b c = innerRightZ 2 b c * associatorZ 2 b c := by
  fin_cases b <;> fin_cases c <;> decide +kernel

theorem right1Middle2_eq (b c : ZMod 8) : right1Middle2 b c = associatorInverseZ 2 c b * right0Middle2 b c := by
  fin_cases b <;> fin_cases c <;> decide +kernel

theorem right2Middle2_eq (b c : ZMod 8) : right2Middle2 b c = innerLeftZ 2 c b * right1Middle2 b c := by
  fin_cases b <;> fin_cases c <;> decide +kernel

theorem leftFinal2 (b c : ZMod 8) :
    ((-1 : ℤ) ^ (leftScaleBit 2 b c).val * positiveScale (leftScaleExponent 2 b c)) •
      (associatorZ b c 2 * left0Middle2 b c) =
    negativeScale (leftScaleExponent 2 b c) • (innerRightZ b 2 c * left1Middle2 b c) := by
  fin_cases b <;> fin_cases c <;> decide +kernel

theorem rightFinal2 (b c : ZMod 8) :
    ((-1 : ℤ) ^ (rightScaleBit 2 b c).val * positiveScale (rightScaleExponent 2 b c) *
      (RMod.ConstructiveConnectorTable.inverseScale 2 c b : ℤ)) • outerLeftZ 2 b c =
    negativeScale (rightScaleExponent 2 b c) • (associatorZ c 2 b * right2Middle2 b c) := by
  fin_cases b <;> fin_cases c <;> decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor
