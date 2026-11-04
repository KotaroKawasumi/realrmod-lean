import RMod.Classification.Instances.EndFunctors
import RMod.Classification.Instances.TensorFunctors
import RMod.Classification.Instances.TensorEndomorphisms
import Superfusion.Super.TensorGradingUnitor

/-!
# The graded tensor-endomorphism algebra map

Tensoring an endomorphism with an identity gives two algebra maps. Signed
interchange says that their homogeneous images supercommute. Mathlib's
universal property of the graded tensor product then gives the algebra
map, whose underlying linear map is exactly categorical tensoring.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification

open CategoryTheory Superfusion Superfusion.Category GradedTensorProduct
open scoped TensorProduct

variable (C : WeaklyPointedSuperfusion.{u, v}) (X Y : LinearCategory C)

attribute [local implicit_reducible] CategoryTheory.End
  tensorLeftData tensorRightData tensorLeftSuperfunctor tensorRightSuperfunctor
  Superfunctor.toFunctor

theorem tensorEnd_factor_mul (f : End X) (g : End Y) :
    (tensorRightSuperfunctor C Y).endAlgHom X f *
      (tensorLeftSuperfunctor C X).endAlgHom Y g = C.data.tensorHom f g := by
  change C.data.comp (C.data.tensorHom (C.data.id X) g)
    (C.data.tensorHom f (C.data.id Y)) = C.data.tensorHom f g
  rw [interchange_second_even C.laws _ _ _ _ (C.laws.id_even Y),
    C.laws.id_comp, C.laws.comp_id]

theorem tensorEnd_factors_anticommute {i j : ZMod 2}
    (f : endGrading (K := ℝ) X i) (g : endGrading (K := ℝ) Y j) :
    (tensorRightSuperfunctor C Y).endAlgHom X f *
        (tensorLeftSuperfunctor C X).endAlgHom Y g =
      (-1 : ℤˣ) ^ (j * i) •
        ((tensorLeftSuperfunctor C X).endAlgHom Y g *
          (tensorRightSuperfunctor C Y).endAlgHom X f) := by
  have hs : (tensorLeftSuperfunctor C X).endAlgHom Y g *
      (tensorRightSuperfunctor C Y).endAlgHom X f =
      (-1 : ℤˣ) ^ (j * i) •
        ((tensorRightSuperfunctor C Y).endAlgHom X f *
          (tensorLeftSuperfunctor C X).endAlgHom Y g) := by
    rw [tensorEnd_factor_mul]
    rw [Units.smul_def, ← sgn_eq_neg_one_uzpow, ← koszulSign_smul_eq_sgn_zsmul ℝ]
    change C.data.comp (C.data.tensorHom f.val (C.data.id Y))
      (C.data.tensorHom (C.data.id X) g.val) =
        C.data.smul ((-1 : ℝ) ^ (j * i).val) (C.data.tensorHom f.val g.val)
    rw [C.laws.super_interchange _ _ _ _ g.property f.property,
      C.laws.comp_id, C.laws.id_comp]
  rw [hs, smul_smul, Int.units_mul_self, one_smul]

noncomputable def tensorEndAlgHom :
    (endGrading (K := ℝ) X ᵍ⊗[ℝ] endGrading (K := ℝ) Y) →ₐ[ℝ]
      End (C := LinearCategory C) (C.data.tensorObj X Y) :=
  GradedTensorProduct.lift _ _ ((tensorRightSuperfunctor C Y).endAlgHom X)
    ((tensorLeftSuperfunctor C X).endAlgHom Y)
    (fun {_ _} f g => tensorEnd_factors_anticommute C X Y f g)

@[simp]
theorem tensorEndAlgHom_tmul (f : End X) (g : End Y) :
    tensorEndAlgHom C X Y (f ᵍ⊗ₜ[ℝ] g) = C.data.tensorHom f g :=
  tensorEnd_factor_mul C X Y f g

theorem tensorEndAlgHom_linear :
    (tensorEndAlgHom C X Y).toLinearMap =
      (tensorEndLinear C X Y).comp
        (GradedTensorProduct.of ℝ (endGrading (K := ℝ) X)
          (endGrading (K := ℝ) Y)).symm.toLinearMap := by
  apply GradedTensorProduct.hom_ext
  apply TensorProduct.ext'
  intro f g
  exact tensorEndAlgHom_tmul C X Y f g

theorem tensorEndAlgHom_homogeneous :
    IsHomogeneousHom (tensorGrading (endGrading (K := ℝ) X) (endGrading (K := ℝ) Y))
      (endGrading (K := ℝ) (C := LinearCategory C) (C.data.tensorObj X Y))
      (tensorEndAlgHom C X Y) := by
  intro a t ht
  refine tensorGrading_induction _ _ ht
    (p := fun w => tensorEndAlgHom C X Y w ∈
      endGrading (K := ℝ) (C := LinearCategory C) (C.data.tensorObj X Y) a) ?_ ?_ ?_ ?_
  · intro i j f g hij hf hg
    rw [tensorEndAlgHom_tmul]
    exact hij ▸ C.laws.tensor_grade f g hf hg
  · rw [map_zero]
    exact zero_mem _
  · intro s t hs ht
    rw [map_add]
    exact add_mem hs ht
  · intro r t ht
    rw [map_smul]
    exact Submodule.smul_mem _ r ht

end RMod.Classification
