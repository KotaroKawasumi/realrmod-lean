import RMod.BrundanEllis.StackingReferenceHexagonMiddle3
import RMod.BrundanEllis.StackingReferenceSparseMatrixCheck

/-! Seven closed product identities for one reference triple.
The proof uses only verified atomic maps and ordinary kernel reduction. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
set_option linter.unusedSimpArgs false
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases3
open Superfusion

theorem left0Middle3_eq_case_0_5 : left0Middle3 0 5 = outerRightZ 3 0 5 * associatorZ 3 0 5 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem left1Middle3_eq_case_0_5 : left1Middle3 0 5 = associatorZ 0 3 5 * innerLeftZ 3 0 5 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem right0Middle3_eq_case_0_5 : right0Middle3 0 5 = innerRightZ 3 0 5 * associatorZ 3 0 5 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem right1Middle3_eq_case_0_5 : right1Middle3 0 5 = associatorInverseZ 3 5 0 * right0Middle3 0 5 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem right2Middle3_eq_case_0_5 : right2Middle3 0 5 = innerLeftZ 3 5 0 * right1Middle3 0 5 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem leftFinal3_case_0_5 : ((-1 : ℤ) ^ (leftScaleBit 3 0 5).val * positiveScale (leftScaleExponent 3 0 5)) •
      (associatorZ 0 5 3 * left0Middle3 0 5) = negativeScale (leftScaleExponent 3 0 5) • (innerRightZ 0 3 5 * left1Middle3 0 5) := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem rightFinal3_case_0_5 : ((-1 : ℤ) ^ (rightScaleBit 3 0 5).val * positiveScale (rightScaleExponent 3 0 5) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 5 0 : ℤ)) • outerLeftZ 3 0 5 = negativeScale (rightScaleExponent 3 0 5) • (associatorZ 5 3 0 * right2Middle3 0 5) := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases3
