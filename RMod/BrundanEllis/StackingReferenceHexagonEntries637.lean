import RMod.BrundanEllis.StackingReferenceHexagonMiddle6
import RMod.BrundanEllis.StackingReferenceSparseMatrixCheck

/-! Seven closed product identities for one reference triple.
The proof uses only verified atomic maps and ordinary kernel reduction. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
set_option linter.unusedSimpArgs false
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases6
open Superfusion

theorem left0Middle6_eq_case_3_7 : left0Middle6 3 7 = outerRightZ 6 3 7 * associatorZ 6 3 7 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem left1Middle6_eq_case_3_7 : left1Middle6 3 7 = associatorZ 3 6 7 * innerLeftZ 6 3 7 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem right0Middle6_eq_case_3_7 : right0Middle6 3 7 = innerRightZ 6 3 7 * associatorZ 6 3 7 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem right1Middle6_eq_case_3_7 : right1Middle6 3 7 = associatorInverseZ 6 7 3 * right0Middle6 3 7 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem right2Middle6_eq_case_3_7 : right2Middle6 3 7 = innerLeftZ 6 7 3 * right1Middle6 3 7 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem leftFinal6_case_3_7 : ((-1 : ℤ) ^ (leftScaleBit 6 3 7).val * positiveScale (leftScaleExponent 6 3 7)) •
      (associatorZ 3 7 6 * left0Middle6 3 7) = negativeScale (leftScaleExponent 6 3 7) • (innerRightZ 3 6 7 * left1Middle6 3 7) := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem rightFinal6_case_3_7 : ((-1 : ℤ) ^ (rightScaleBit 6 3 7).val * positiveScale (rightScaleExponent 6 3 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 7 3 : ℤ)) • outerLeftZ 6 3 7 = negativeScale (rightScaleExponent 6 3 7) • (associatorZ 7 6 3 * right2Middle6 3 7) := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases6
