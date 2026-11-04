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

theorem left0Middle3_eq_case_6_0 : left0Middle3 6 0 = outerRightZ 3 6 0 * associatorZ 3 6 0 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem left1Middle3_eq_case_6_0 : left1Middle3 6 0 = associatorZ 6 3 0 * innerLeftZ 3 6 0 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem right0Middle3_eq_case_6_0 : right0Middle3 6 0 = innerRightZ 3 6 0 * associatorZ 3 6 0 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem right1Middle3_eq_case_6_0 : right1Middle3 6 0 = associatorInverseZ 3 0 6 * right0Middle3 6 0 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem right2Middle3_eq_case_6_0 : right2Middle3 6 0 = innerLeftZ 3 0 6 * right1Middle3 6 0 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem leftFinal3_case_6_0 : ((-1 : ℤ) ^ (leftScaleBit 3 6 0).val * positiveScale (leftScaleExponent 3 6 0)) •
      (associatorZ 6 0 3 * left0Middle3 6 0) = negativeScale (leftScaleExponent 3 6 0) • (innerRightZ 6 3 0 * left1Middle3 6 0) := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem rightFinal3_case_6_0 : ((-1 : ℤ) ^ (rightScaleBit 3 6 0).val * positiveScale (rightScaleExponent 3 6 0) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 0 6 : ℤ)) • outerLeftZ 3 6 0 = negativeScale (rightScaleExponent 3 6 0) • (associatorZ 0 3 6 * right2Middle3 6 0) := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases3
