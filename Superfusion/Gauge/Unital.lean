/-
Superfusion / Gauge / Unital

Invariant unit data for a division fusion gauge.  Unlike the old size-order
convention, this structure identifies the two unit fusion columns with the
regular modules and records all actions and the grading.  It does not impose
literal matrix sizes, so it is preserved under equivalent presentations.
-/
import Superfusion.Wedderburn.FusionColumn

namespace Superfusion

open scoped TensorProduct

namespace DivisionFusionGauge

universe u v

variable {K : Type u} [Field K] [Invertible (2 : K)]
variable {G : Type v} [AddGroup G]

/-- Transport the coefficient algebra along `0 + a = a`. -/
noncomputable def zeroAddEquiv (Γ : DivisionFusionGauge K G) (a : G) :
    SuperAlgEquiv (Γ.D (0 + a)) (Γ.D a) :=
  superAlgebraFamilyCast Γ.D (zero_add a)

/-- Transport the coefficient algebra along `a + 0 = a`. -/
noncomputable def addZeroEquiv (Γ : DivisionFusionGauge K G) (a : G) :
    SuperAlgEquiv (Γ.D (a + 0)) (Γ.D a) :=
  superAlgebraFamilyCast Γ.D (add_zero a)

/-- Invariant unital normalization of a division fusion gauge.  The two
fusion columns involving the neutral label are identified, as graded
bimodules, with the appropriate regular right module. -/
structure UnitalNormalization (Γ : DivisionFusionGauge K G) where
  /-- The representative at the neutral label is the scalar superalgebra. -/
  unitAlg : SuperAlgEquiv (Γ.D 0) (SuperAlgebra.base K)
  /-- The left-unit fusion column is the regular right module. -/
  leftColumnEquiv : ∀ a,
    Bimod.FusionColumn (Γ.fuse 0 a) ≃ₗ[K] (Γ.D a).carrier
  /-- The right-unit fusion column is the regular right module. -/
  rightColumnEquiv : ∀ a,
    Bimod.FusionColumn (Γ.fuse a 0) ≃ₗ[K] (Γ.D a).carrier
  /-- The `D₀` slot of the left-unit column acts through scalars. -/
  left_zero_action : ∀ a (x : (Γ.D 0).carrier)
      (m : Bimod.FusionColumn (Γ.fuse 0 a)),
    leftColumnEquiv a
        (GradedTensorProduct.includeLeft (Γ.D 0).grading (Γ.D a).grading x • m)
      = unitAlg.toAlgEquiv x • leftColumnEquiv a m
  /-- The `Dₐ` slot of the left-unit column acts by left multiplication. -/
  left_main_action : ∀ a (x : (Γ.D a).carrier)
      (m : Bimod.FusionColumn (Γ.fuse 0 a)),
    leftColumnEquiv a
        (GradedTensorProduct.includeRight (Γ.D 0).grading (Γ.D a).grading x • m)
      = x * leftColumnEquiv a m
  /-- The coefficient action is regular on the left-unit column. -/
  left_coeff_action : ∀ a (x : (Γ.D (0 + a)).carrier)
      (m : Bimod.FusionColumn (Γ.fuse 0 a)),
    leftColumnEquiv a (MulOpposite.op x • m) =
      leftColumnEquiv a m * (zeroAddEquiv Γ a).toAlgEquiv x
  /-- The left-unit column identification preserves each homogeneous part. -/
  left_map_grading : ∀ a i,
    (Bimod.FusionColumn.grading (Γ.fuse 0 a) i).map
        (leftColumnEquiv a).toLinearMap = (Γ.D a).grading i
  /-- The `Dₐ` slot of the right-unit column acts by left multiplication. -/
  right_main_action : ∀ a (x : (Γ.D a).carrier)
      (m : Bimod.FusionColumn (Γ.fuse a 0)),
    rightColumnEquiv a
        (GradedTensorProduct.includeLeft (Γ.D a).grading (Γ.D 0).grading x • m)
      = x * rightColumnEquiv a m
  /-- The `D₀` slot of the right-unit column acts through scalars. -/
  right_zero_action : ∀ a (x : (Γ.D 0).carrier)
      (m : Bimod.FusionColumn (Γ.fuse a 0)),
    rightColumnEquiv a
        (GradedTensorProduct.includeRight (Γ.D a).grading (Γ.D 0).grading x • m)
      = unitAlg.toAlgEquiv x • rightColumnEquiv a m
  /-- The coefficient action is regular on the right-unit column. -/
  right_coeff_action : ∀ a (x : (Γ.D (a + 0)).carrier)
      (m : Bimod.FusionColumn (Γ.fuse a 0)),
    rightColumnEquiv a (MulOpposite.op x • m) =
      rightColumnEquiv a m * (addZeroEquiv Γ a).toAlgEquiv x
  /-- The right-unit column identification preserves each homogeneous part. -/
  right_map_grading : ∀ a i,
    (Bimod.FusionColumn.grading (Γ.fuse a 0) i).map
        (rightColumnEquiv a).toLinearMap = (Γ.D a).grading i
  /-- The left and right unit identifications agree at the neutral label. -/
  unit_compatibility : leftColumnEquiv 0 = rightColumnEquiv 0

end DivisionFusionGauge

end Superfusion
