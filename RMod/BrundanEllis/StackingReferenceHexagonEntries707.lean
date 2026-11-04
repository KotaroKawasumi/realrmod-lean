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

theorem left0Middle7_eq_case_0_7 : left0Middle7 0 7 = outerRightZ 7 0 7 * associatorZ 7 0 7 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem left1Middle7_eq_case_0_7 : left1Middle7 0 7 = associatorZ 0 7 7 * innerLeftZ 7 0 7 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem right0Middle7_eq_case_0_7 : right0Middle7 0 7 = innerRightZ 7 0 7 * associatorZ 7 0 7 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem right1Middle7_eq_case_0_7 : right1Middle7 0 7 = associatorInverseZ 7 7 0 * right0Middle7 0 7 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem right2Middle7_eq_case_0_7 : right2Middle7 0 7 = innerLeftZ 7 7 0 * right1Middle7 0 7 := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem leftFinal7_case_0_7 : ((-1 : ℤ) ^ (leftScaleBit 7 0 7).val * positiveScale (leftScaleExponent 7 0 7)) •
      (associatorZ 0 7 7 * left0Middle7 0 7) = negativeScale (leftScaleExponent 7 0 7) • (innerRightZ 0 7 7 * left1Middle7 0 7) := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

theorem rightFinal7_case_0_7 : ((-1 : ℤ) ^ (rightScaleBit 7 0 7).val * positiveScale (rightScaleExponent 7 0 7) *
      (RMod.ConstructiveConnectorTable.inverseScale 7 7 0 : ℤ)) • outerLeftZ 7 0 7 = negativeScale (rightScaleExponent 7 0 7) • (associatorZ 7 7 0 * right2Middle7 0 7) := by
  simp only [← tripleSparseMul_eq]
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonCases7
