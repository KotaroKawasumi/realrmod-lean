import RMod.BrundanEllis.StackingReferenceHexagonMiddle5
import RMod.BrundanEllis.StackingReferenceSparseMatrixCheck

/-! Seven closed product identities for one reference triple.
The proof uses only verified atomic maps and ordinary kernel reduction. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
set_option linter.unusedSimpArgs false
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases5
open Superfusion

theorem left0Middle5_eq_case_0_7 : left0Middle5 0 7 = outerRightZ 5 0 7 * associatorZ 5 0 7 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem left1Middle5_eq_case_0_7 : left1Middle5 0 7 = associatorZ 0 5 7 * innerLeftZ 5 0 7 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem right0Middle5_eq_case_0_7 : right0Middle5 0 7 = innerRightZ 5 0 7 * associatorZ 5 0 7 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem right1Middle5_eq_case_0_7 : right1Middle5 0 7 = associatorInverseZ 5 7 0 * right0Middle5 0 7 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem right2Middle5_eq_case_0_7 : right2Middle5 0 7 = innerLeftZ 5 7 0 * right1Middle5 0 7 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem leftFinal5_case_0_7 : ((-1 : ℤ) ^ (leftScaleBit 5 0 7).val * positiveScale (leftScaleExponent 5 0 7)) •
      (associatorZ 0 7 5 * left0Middle5 0 7) = negativeScale (leftScaleExponent 5 0 7) • (innerRightZ 0 5 7 * left1Middle5 0 7) := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem rightFinal5_case_0_7 : ((-1 : ℤ) ^ (rightScaleBit 5 0 7).val * positiveScale (rightScaleExponent 5 0 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 5 7 0 : ℤ)) • outerLeftZ 5 0 7 = negativeScale (rightScaleExponent 5 0 7) • (associatorZ 7 5 0 * right2Middle5 0 7) := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases5
