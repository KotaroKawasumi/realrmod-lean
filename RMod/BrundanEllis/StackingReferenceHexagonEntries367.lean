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

theorem left0Middle3_eq_case_6_7 : left0Middle3 6 7 = outerRightZ 3 6 7 * associatorZ 3 6 7 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem left1Middle3_eq_case_6_7 : left1Middle3 6 7 = associatorZ 6 3 7 * innerLeftZ 3 6 7 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem right0Middle3_eq_case_6_7 : right0Middle3 6 7 = innerRightZ 3 6 7 * associatorZ 3 6 7 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem right1Middle3_eq_case_6_7 : right1Middle3 6 7 = associatorInverseZ 3 7 6 * right0Middle3 6 7 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem right2Middle3_eq_case_6_7 : right2Middle3 6 7 = innerLeftZ 3 7 6 * right1Middle3 6 7 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem leftFinal3_case_6_7 : ((-1 : ℤ) ^ (leftScaleBit 3 6 7).val * positiveScale (leftScaleExponent 3 6 7)) •
      (associatorZ 6 7 3 * left0Middle3 6 7) = negativeScale (leftScaleExponent 3 6 7) • (innerRightZ 6 3 7 * left1Middle3 6 7) := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem rightFinal3_case_6_7 : ((-1 : ℤ) ^ (rightScaleBit 3 6 7).val * positiveScale (rightScaleExponent 3 6 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 3 7 6 : ℤ)) • outerLeftZ 3 6 7 = negativeScale (rightScaleExponent 3 6 7) • (associatorZ 7 3 6 * right2Middle3 6 7) := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases3
