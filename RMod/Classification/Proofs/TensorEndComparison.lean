import RMod.Classification.Instances.TensorEndComparison

/-!
# Tensor comparison acts factorwise on actual tensor morphisms

The tensor-endomorphism equivalences send pure algebra tensors to the
category's tensor morphisms. Tensor congruence therefore makes the
comparison act on these morphisms by the two specified factor maps.
The inherited grading equality also reflects each homogeneous degree.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory Superfusion Superfusion.Category GradedTensorProduct
open scoped TensorProduct

attribute [local implicit_reducible] CategoryTheory.End
  Superfusion.Category.endSuperAlgebra Superfusion.Category.endGrading

variable (C D : WeaklyPointedSuperfusion.{0, 0}) (S T : LinearCategory C) (X Y : LinearCategory D)
  (hT : C.data.IsSimple T) (hY : D.data.IsSimple Y)
  (a : SuperAlgEquiv (endSuperAlgebra (K := ℝ) S) (endSuperAlgebra (K := ℝ) X))
  (b : SuperAlgEquiv (endSuperAlgebra (K := ℝ) T) (endSuperAlgebra (K := ℝ) Y))

theorem tensorEndComparison_tensorHom (f : End S) (g : End T) :
    (tensorEndComparison C D S T X Y hT hY a b).toAlgEquiv (C.data.tensorHom f g) =
      D.data.tensorHom (a.toAlgEquiv f) (b.toAlgEquiv g) := by
  have hs : (tensorEndSuperEquiv C S T hT).toAlgEquiv (show (endGrading (K := ℝ) S) ᵍ⊗[ℝ] (endGrading (K := ℝ) T) from f ᵍ⊗ₜ[ℝ] g) = C.data.tensorHom f g :=
    tensorEndAlgHom_tmul C S T f g
  change (tensorEndSuperEquiv D X Y hY).toAlgEquiv
    ((a.gtensorCongr b).toAlgEquiv
      ((tensorEndSuperEquiv C S T hT).toAlgEquiv.symm (C.data.tensorHom f g))) = _
  rw [← hs, AlgEquiv.symm_apply_apply, SuperAlgEquiv.gtensorCongr_tmul]
  exact tensorEndAlgHom_tmul D X Y _ _

theorem tensorEndComparison_grade_iff {p : ZMod 2}
    (f : @End (LinearCategory C) _ (C.data.tensorObj S T)) :
    D.data.IsHomogeneous p ((tensorEndComparison C D S T X Y hT hY a b).toAlgEquiv f) ↔
      C.data.IsHomogeneous p f := by
  let e := tensorEndComparison C D S T X Y hT hY a b
  exact (Superfusion.mem_iff_map_mem _ _ e.toAlgEquiv e.map_grading).symm

end RMod.Classification
