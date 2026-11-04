import RMod.BrundanEllis.StackingReferenceCategoricalHexagon
import RMod.BrundanEllis.StackingReferenceHexagonExamples

/-! Two nontrivial actual categorical hexagons, with their finite coefficient
hypotheses discharged by the ordinary Lean kernel. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor
open Superfusion.RMod.FromRawDCT

/-- The degree-four cycle satisfies the first hexagon with the actual reference maps. -/
example : leftHexagonShortMap 1 4 4 = leftHexagonLongMap 1 4 4 :=
  leftHexagon_categorical 1 4 4 leftHexagon_144

/-- Three odd type-one atoms exhibit the nontrivial sign in the second hexagon. -/
example : outerLeftMap 1 1 1 = Hom.smul (-1) (rightHexagonLongMap 1 1 1) := by
  have h := rightHexagon_categorical 1 1 1 rightHexagon_111
  change outerLeftMap 1 1 1 = Hom.smul (-1) (rightHexagonLongMap 1 1 1) at h
  exact h

end RMod.BrundanEllis.Stacking.ReferenceCommutor
