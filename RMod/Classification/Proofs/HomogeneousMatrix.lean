import RMod.Classification.Instances.HomogeneousMatrix
import RMod.Classification.Instances.EndGrading
import Superfusion.Super.MatrixSuperCoeff

/-!
# The grading of an endomorphism matrix

An endomorphism of degree a has entry (i,j) in degree a + parity(i) +
parity(j). Conversely every such matrix reconstructs an endomorphism of
degree a. Both directions are needed to compare Clifford algebras.
-/

set_option autoImplicit false

namespace RMod.Classification.HomogeneousSum

open CategoryTheory

attribute [local implicit_reducible] CategoryTheory.End Matrix

variable {C : WeaklyPointedSuperfusion.{0, 0}}
  {X Y : LinearCategory C} {n : ℕ}
  (d : HomogeneousSum C.data X Y n)

theorem toMatrix_grade {a : ZMod 2} {f : End Y}
    (hf : C.data.IsHomogeneous a f) (i j : Fin n) :
    C.data.IsHomogeneous (a + d.data.parity i + d.data.parity j) (toMatrix d f i j) := by
  have h := C.laws.comp_grade _ _ (d.laws.inclusion_grade j)
    (C.laws.comp_grade _ _ hf (d.laws.projection_grade i))
  have hp : d.data.parity j + (a + d.data.parity i) =
      a + d.data.parity i + d.data.parity j := add_comm _ _
  rw [hp] at h
  exact h

theorem fromMatrix_grade {a : ZMod 2} {m : Matrix (Fin n) (Fin n) (End X)}
    (hm : ∀ i j, C.data.IsHomogeneous
      (a + d.data.parity i + d.data.parity j) (m i j)) :
    C.data.IsHomogeneous a (fromMatrix d m) := by
  change fromMatrix d m ∈ LinearCategory.grade C Y Y a
  apply Submodule.sum_mem
  intro j _
  apply Submodule.sum_mem
  intro i _
  have h := C.laws.comp_grade _ _ (d.laws.projection_grade j)
    (C.laws.comp_grade _ _ (hm i j) (d.laws.inclusion_grade i))
  have hp : d.data.parity j +
      ((a + d.data.parity i + d.data.parity j) + d.data.parity i) = a := by
    calc
      _ = a + (d.data.parity i + d.data.parity i) +
          (d.data.parity j + d.data.parity j) := by abel
      _ = a := by simp only [CharTwo.add_self_eq_zero, add_zero]
  rw [hp] at h
  exact h

/-- The matrix equivalence identifies the full graded components. -/
theorem matrixAlgEquiv_grade_iff (a : ZMod 2) (f : End Y) :
    f ∈ LinearCategory.grade C Y Y a ↔
      matrixAlgEquiv d f ∈ Superfusion.matrixGradingA d.data.parity
        (Superfusion.Category.endSuperAlgebra (K := ℝ) X).grading a := by
  constructor
  · intro hf
    exact toMatrix_grade d hf
  · intro hm
    have h := fromMatrix_grade d hm
    change C.data.IsHomogeneous a (fromMatrix d (toMatrix d f)) at h
    rwa [fromMatrix_toMatrix] at h

end RMod.Classification.HomogeneousSum
