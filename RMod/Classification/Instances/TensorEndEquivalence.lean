import RMod.Classification.Instances.TensorEndAlgebra
import RMod.Classification.Proofs.TensorEndSurjection

/-!
# Tensor-endomorphism superalgebra equivalences

The inverse is chosen only after injectivity and surjectivity of the actual
tensor map have been proved. Internal gradings and bijectivity upgrade
preservation to equality of the graded pieces, using the existing graded
transfer theorem. Thus the inverse preserves parity as well.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory Superfusion Superfusion.Category GradedTensorProduct

variable (C : WeaklyPointedSuperfusion.{0, 0}) (X Y : LinearCategory C)

theorem tensorEndAlgHom_injective : Function.Injective (tensorEndAlgHom C X Y) := by
  change Function.Injective (tensorEndAlgHom C X Y).toLinearMap
  rw [tensorEndAlgHom_linear]
  exact (tensorEndLinear_injective C X Y).comp
    (GradedTensorProduct.of ℝ (endGrading (K := ℝ) X) (endGrading (K := ℝ) Y)).symm.injective

theorem tensorEndAlgHom_bijective (hY : C.data.IsWeaklyInvertible Y) :
    Function.Bijective (tensorEndAlgHom C X Y) := by
  change Function.Bijective (tensorEndAlgHom C X Y).toLinearMap
  rw [tensorEndAlgHom_linear]
  exact (tensorEndLinear_bijective_of_weaklyInvertible C X Y hY).comp
    (GradedTensorProduct.of ℝ (endGrading (K := ℝ) X) (endGrading (K := ℝ) Y)).symm.bijective

noncomputable def tensorEndSuperEquivOfWeaklyInvertible (hY : C.data.IsWeaklyInvertible Y) :
    SuperAlgEquiv ((endSuperAlgebra (K := ℝ) X).gtensor (endSuperAlgebra (K := ℝ) Y))
      (endSuperAlgebra (K := ℝ) (C := LinearCategory C) (C.data.tensorObj X Y)) where
  toAlgEquiv := AlgEquiv.ofBijective (tensorEndAlgHom C X Y) (tensorEndAlgHom_bijective C X Y hY)
  map_grading i := map_grading_of_bijective _ _ (tensorEndAlgHom C X Y)
    (tensorEndAlgHom_homogeneous C X Y) (tensorEndAlgHom_bijective C X Y hY) i

noncomputable def tensorEndSuperEquiv (hY : C.data.IsSimple Y) :
    SuperAlgEquiv ((endSuperAlgebra (K := ℝ) X).gtensor (endSuperAlgebra (K := ℝ) Y))
      (endSuperAlgebra (K := ℝ) (C := LinearCategory C) (C.data.tensorObj X Y)) :=
  tensorEndSuperEquivOfWeaklyInvertible C X Y (C.laws.weakly_pointed Y hY)

end RMod.Classification
