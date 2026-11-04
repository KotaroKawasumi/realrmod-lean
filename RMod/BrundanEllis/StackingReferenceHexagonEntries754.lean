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

theorem left0Middle7_eq_case_5_4 : left0Middle7 5 4 = outerRightZ 7 5 4 * associatorZ 7 5 4 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem left1Middle7_eq_case_5_4 : left1Middle7 5 4 = associatorZ 5 7 4 * innerLeftZ 7 5 4 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem right0Middle7_eq_case_5_4 : right0Middle7 5 4 = innerRightZ 7 5 4 * associatorZ 7 5 4 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem right1Middle7_eq_case_5_4 : right1Middle7 5 4 = associatorInverseZ 7 4 5 * right0Middle7 5 4 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem right2Middle7_eq_case_5_4 : right2Middle7 5 4 = innerLeftZ 7 4 5 * right1Middle7 5 4 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem leftFinal7_case_5_4 : ((-1 : ℤ) ^ (leftScaleBit 7 5 4).val * positiveScale (leftScaleExponent 7 5 4)) •
      (associatorZ 5 4 7 * left0Middle7 5 4) = negativeScale (leftScaleExponent 7 5 4) • (innerRightZ 5 7 4 * left1Middle7 5 4) := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem rightFinal7_case_5_4 : ((-1 : ℤ) ^ (rightScaleBit 7 5 4).val * positiveScale (rightScaleExponent 7 5 4) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 4 5 : ℤ)) • outerLeftZ 7 5 4 = negativeScale (rightScaleExponent 7 5 4) • (associatorZ 4 7 5 * right2Middle7 5 4) := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases7
