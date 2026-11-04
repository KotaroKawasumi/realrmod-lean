import RMod.BrundanEllis.StackingReferenceLeftHexagon0
import RMod.BrundanEllis.StackingReferenceRightHexagon0
import RMod.BrundanEllis.StackingReferenceLeftHexagon1
import RMod.BrundanEllis.StackingReferenceRightHexagon1
import RMod.BrundanEllis.StackingReferenceLeftHexagon2
import RMod.BrundanEllis.StackingReferenceRightHexagon2
import RMod.BrundanEllis.StackingReferenceLeftHexagon3
import RMod.BrundanEllis.StackingReferenceRightHexagon3
import RMod.BrundanEllis.StackingReferenceLeftHexagon4
import RMod.BrundanEllis.StackingReferenceRightHexagon4
import RMod.BrundanEllis.StackingReferenceLeftHexagon5
import RMod.BrundanEllis.StackingReferenceRightHexagon5
import RMod.BrundanEllis.StackingReferenceLeftHexagon6
import RMod.BrundanEllis.StackingReferenceRightHexagon6
import RMod.BrundanEllis.StackingReferenceLeftHexagon7
import RMod.BrundanEllis.StackingReferenceRightHexagon7
import RMod.BrundanEllis.StackingReferenceHexagonNormalization

/-! All normalized reference hexagon coefficient identities. These statements
compare the explicit coordinate diagrams; extending them to the full exterior
monoidal functor is a separate construction. -/
noncomputable section
set_option autoImplicit false
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor
open Superfusion Superfusion.RMod.RawDCT

/-- The first coefficient hexagon for every reference triple. -/
theorem leftHexagon_equation (a b c : ZMod 8) : LeftEquation a b c := by
  fin_cases a
  · exact leftHexagon_0 b c
  · exact leftHexagon_1 b c
  · exact leftHexagon_2 b c
  · exact leftHexagon_3 b c
  · exact leftHexagon_4 b c
  · exact leftHexagon_5 b c
  · exact leftHexagon_6 b c
  · exact leftHexagon_7 b c

/-- The second coefficient hexagon, including its quadratic defect. -/
theorem rightHexagon_equation (a b c : ZMod 8) : RightEquation a b c := by
  fin_cases a
  · exact rightHexagon_0 b c
  · exact rightHexagon_1 b c
  · exact rightHexagon_2 b c
  · exact rightHexagon_3 b c
  · exact rightHexagon_4 b c
  · exact rightHexagon_5 b c
  · exact rightHexagon_6 b c
  · exact rightHexagon_7 b c

/-- Exact equality after the prescribed real normalization. -/
theorem leftHexagon_real (a b c : ZMod 8) :
    ((associatorScale b c a : ℝ) * normalizingScalar a (b + c) * (associatorScale a b c : ℝ)) •
        (leftShortZ a b c).map ((↑) : ℤ → ℝ) =
      (normalizingScalar a c * (associatorScale b a c : ℝ) * normalizingScalar a b) •
        (leftLongZ a b c).map ((↑) : ℤ → ℝ) :=
  leftHexagon_normalized a b c (leftHexagon_equation a b c)

/-- The normalized second hexagon has exactly the specified sign. -/
theorem rightHexagon_real (a b c : ZMod 8) :
    ((RMod.ConstructiveConnectorTable.inverseScale a c b : ℝ) * normalizingScalar (a + b) c) •
        (outerLeftZ a b c).map ((↑) : ℤ → ℝ) =
      (paritySign (rightDefect a b c) *
        ((associatorScale c a b : ℝ) * normalizingScalar a c * (associatorScale a c b : ℝ)⁻¹ *
          normalizingScalar b c * (associatorScale a b c : ℝ))) •
        (rightLongZ a b c).map ((↑) : ℤ → ℝ) :=
  rightHexagon_normalized a b c (rightHexagon_equation a b c)

end RMod.BrundanEllis.Stacking.ReferenceCommutor
