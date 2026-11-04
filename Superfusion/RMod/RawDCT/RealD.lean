import Superfusion.RMod.Constructive.CoordinateCategoryLaws
import Superfusion.RMod.RawDCT.D

/-!
# Concrete computable real coefficient family

This file constructs the `K = ℝ`, `G = ZMod 8` inhabitant of the abstract
structures in `D.lean`.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT

open RModCoordinate

/-- Coordinate data for one real Brauer--Wall label. -/
def coordinateSuperAlgebraData (a : ZMod 8) : SuperAlgebraData ℝ where
  carrier := Coeff a
  zero := Coeff.zero a
  add := Coeff.add a
  neg := Coeff.neg a
  one := Coeff.one a
  mul := Coeff.mul a
  smul := Coeff.smul a
  component := Coeff.component a

/-- The eight executable raw coefficient algebras. -/
def realDData : DData where
  algebra := coordinateSuperAlgebraData

/-- The coordinate proofs attached only after the executable algebra exists. -/
theorem coordinateSuperAlgebraLaws (a : ZMod 8) :
    SuperAlgebraLaws (coordinateSuperAlgebraData a) where
  add_assoc := Coeff.add_assoc a
  add_comm := Coeff.add_comm a
  zero_add := Coeff.zero_add a
  add_zero := Coeff.add_zero a
  neg_add := Coeff.neg_add a
  add_neg := Coeff.add_neg a
  mul_assoc := Coeff.mul_assoc a
  one_mul := Coeff.one_mul a
  mul_one := Coeff.mul_one a
  mul_add := Coeff.mul_add a
  add_mul := Coeff.add_mul a
  one_smul := Coeff.one_smul a
  smul_assoc := Coeff.mul_smul a
  add_smul := Coeff.add_smul a
  smul_add := Coeff.smul_add a
  zero_smul := Coeff.zero_smul a
  smul_zero := Coeff.smul_zero a
  smul_mul := Coeff.smul_mul a
  mul_smul := Coeff.mul_smul_right a
  component_zero := Coeff.component_zero a
  component_add := Coeff.component_add a
  component_neg := Coeff.component_neg a
  component_smul := Coeff.component_smul a
  component_idem := Coeff.component_idem a
  component_complement := Coeff.component_complement a
  grade_disjoint := by
    intro i x hx hx'
    apply Coeff.memGrade_disjoint a i
    · exact (Coeff.component_eq_self_iff a i x).1 hx
    · exact (Coeff.component_eq_self_iff a (i + 1) x).1 hx'
  one_mem := (Coeff.component_eq_self_iff a 0 _).2 (Coeff.memGrade_one a)
  mul_mem := by
    intro i j x y hx hy
    apply (Coeff.component_eq_self_iff a (i + j) _).2
    exact Coeff.memGrade_mul a i j
      ((Coeff.component_eq_self_iff a i x).1 hx)
      ((Coeff.component_eq_self_iff a j y).1 hy)

/-- Laws for all eight exact records in `realDData`. -/
theorem realDLaws : DLaws realDData where
  algebra_laws := coordinateSuperAlgebraLaws

/-- The completed raw coefficient family. -/
def realD : D where
  data := realDData
  laws := realDLaws

/-! Small closed reductions for the concrete data layer. -/

example : (realDData.algebra 0).one (0 : Fin 1) = 1 := rfl

example :
    (realDData.algebra 4).component 0
      ((realDData.algebra 4).one) (0 : Fin 4) = 1 := rfl

end Superfusion.RMod.RawDCT
