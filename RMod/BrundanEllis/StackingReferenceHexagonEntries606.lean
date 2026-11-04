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

theorem left0Middle6_eq_case_0_6 : left0Middle6 0 6 = outerRightZ 6 0 6 * associatorZ 6 0 6 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem left1Middle6_eq_case_0_6 : left1Middle6 0 6 = associatorZ 0 6 6 * innerLeftZ 6 0 6 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem right0Middle6_eq_case_0_6 : right0Middle6 0 6 = innerRightZ 6 0 6 * associatorZ 6 0 6 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem right1Middle6_eq_case_0_6 : right1Middle6 0 6 = associatorInverseZ 6 6 0 * right0Middle6 0 6 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem right2Middle6_eq_case_0_6 : right2Middle6 0 6 = innerLeftZ 6 6 0 * right1Middle6 0 6 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem leftFinal6_case_0_6 : ((-1 : ℤ) ^ (leftScaleBit 6 0 6).val * positiveScale (leftScaleExponent 6 0 6)) •
      (associatorZ 0 6 6 * left0Middle6 0 6) = negativeScale (leftScaleExponent 6 0 6) • (innerRightZ 0 6 6 * left1Middle6 0 6) := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem rightFinal6_case_0_6 : ((-1 : ℤ) ^ (rightScaleBit 6 0 6).val * positiveScale (rightScaleExponent 6 0 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 6 6 0 : ℤ)) • outerLeftZ 6 0 6 = negativeScale (rightScaleExponent 6 0 6) • (associatorZ 6 6 0 * right2Middle6 0 6) := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases6
