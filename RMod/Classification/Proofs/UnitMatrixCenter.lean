import RMod.Classification.Instances.HomogeneousHom
import RMod.Classification.Proofs.Endomorphisms
import Mathlib.Algebra.Central.Matrix
import Mathlib.Algebra.Central.Basic

/-!
# Dimensions and the ordinary center of a unit sum

The endomorphism algebra of a homogeneous sum is the ordinary matrix
algebra on its coefficient endomorphisms, regardless of its grading.
For sums of the split real unit, Mathlib's central-matrix theorem therefore
identifies the ordinary center with the real scalars.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

variable {C : WeaklyPointedSuperfusion.{0, 0}}

attribute [local implicit_reducible] CategoryTheory.End

namespace HomogeneousSum

theorem finrank_end {X Y : LinearCategory C} {n : ℕ} (d : HomogeneousSum C.data X Y n) :
    Module.finrank ℝ (End (C := LinearCategory C) Y) =
      n * n * Module.finrank ℝ (End (C := LinearCategory C) X) := by
  rw [(d.matrixAlgEquiv (C := C)).toLinearEquiv.finrank_eq, Module.finrank_matrix]
  simp only [Fintype.card_fin]

theorem unit_end_isCentral {Y : LinearCategory C} {n : ℕ}
    (d : HomogeneousSum C.data C.data.tensorUnit Y n) :
    Algebra.IsCentral ℝ (End (C := LinearCategory C) Y) := by
  letI : Algebra.IsCentral ℝ (End (C := LinearCategory C) C.data.tensorUnit) :=
    Algebra.IsCentral.of_algEquiv ℝ ℝ _ (unitEndEquiv C)
  exact Algebra.IsCentral.of_algEquiv ℝ _ _ (d.matrixAlgEquiv (C := C)).symm

end HomogeneousSum

end RMod.Classification
