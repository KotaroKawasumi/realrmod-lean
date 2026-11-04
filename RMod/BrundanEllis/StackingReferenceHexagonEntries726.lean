import RMod.BrundanEllis.StackingReferenceHexagonMiddle7
import RMod.BrundanEllis.StackingReferenceSparseMatrixCheck

/-! Seven closed product identities for one reference triple.
The proof uses only verified atomic maps and ordinary kernel reduction. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
set_option linter.unusedSimpArgs false
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases7
open Superfusion

theorem left0Middle7_eq_case_2_6 : left0Middle7 2 6 = outerRightZ 7 2 6 * associatorZ 7 2 6 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem left1Middle7_eq_case_2_6 : left1Middle7 2 6 = associatorZ 2 7 6 * innerLeftZ 7 2 6 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem right0Middle7_eq_case_2_6 : right0Middle7 2 6 = innerRightZ 7 2 6 * associatorZ 7 2 6 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem right1Middle7_eq_case_2_6 : right1Middle7 2 6 = associatorInverseZ 7 6 2 * right0Middle7 2 6 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem right2Middle7_eq_case_2_6 : right2Middle7 2 6 = innerLeftZ 7 6 2 * right1Middle7 2 6 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem leftFinal7_case_2_6 : ((-1 : ℤ) ^ (leftScaleBit 7 2 6).val * positiveScale (leftScaleExponent 7 2 6)) •
      (associatorZ 2 6 7 * left0Middle7 2 6) = negativeScale (leftScaleExponent 7 2 6) • (innerRightZ 2 7 6 * left1Middle7 2 6) := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem rightFinal7_case_2_6 : ((-1 : ℤ) ^ (rightScaleBit 7 2 6).val * positiveScale (rightScaleExponent 7 2 6) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 6 2 : ℤ)) • outerLeftZ 7 2 6 = negativeScale (rightScaleExponent 7 2 6) • (associatorZ 6 7 2 * right2Middle7 2 6) := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases7
