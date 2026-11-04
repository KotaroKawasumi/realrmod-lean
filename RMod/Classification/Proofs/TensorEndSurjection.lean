import RMod.Classification.Proofs.TensorEndInjection
import RMod.Classification.Proofs.TensorEndDimension
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Surjectivity of tensoring endomorphisms

The slice proof gives injectivity for arbitrary objects. Weak invertibility
of the second factor supplies equality of the finite real dimensions, so
Mathlib's rank theorem gives surjectivity of this same tensor map.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

attribute [local implicit_reducible] CategoryTheory.End

theorem tensorEndLinear_bijective_of_finrank
    (C : WeaklyPointedSuperfusion.{0, 0}) (X Y : LinearCategory C)
    (hdim : Module.finrank ℝ (End (C := LinearCategory C) (C.data.tensorObj X Y)) =
      Module.finrank ℝ (End (C := LinearCategory C) X) *
        Module.finrank ℝ (End (C := LinearCategory C) Y)) :
    Function.Bijective (tensorEndLinear C X Y) := by
  letI : FiniteDimensional ℝ (End (C := LinearCategory C) X) :=
    LinearCategory.finiteDimensionalHom C X X
  letI : FiniteDimensional ℝ (End (C := LinearCategory C) Y) :=
    LinearCategory.finiteDimensionalHom C Y Y
  letI : FiniteDimensional ℝ (End (C := LinearCategory C) (C.data.tensorObj X Y)) :=
    LinearCategory.finiteDimensionalHom C (C.data.tensorObj X Y) (C.data.tensorObj X Y)
  refine ⟨tensorEndLinear_injective C X Y, ?_⟩
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := tensorEndLinear C X Y) ?_).mp (tensorEndLinear_injective C X Y)
  rw [Module.finrank_tensorProduct, hdim]

theorem tensorEndLinear_bijective_of_weaklyInvertible
    (C : WeaklyPointedSuperfusion.{0, 0}) (X Y : LinearCategory C)
    (hY : C.data.IsWeaklyInvertible Y) : Function.Bijective (tensorEndLinear C X Y) :=
  tensorEndLinear_bijective_of_finrank C X Y (finrank_tensorEnd_of_weaklyInvertible C X Y hY)

theorem tensorEndLinear_bijective (C : WeaklyPointedSuperfusion.{0, 0}) (X Y : LinearCategory C)
    (hY : C.data.IsSimple Y) : Function.Bijective (tensorEndLinear C X Y) :=
  tensorEndLinear_bijective_of_weaklyInvertible C X Y (C.laws.weakly_pointed Y hY)

end RMod.Classification
