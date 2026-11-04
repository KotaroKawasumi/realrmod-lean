import RMod.BrundanEllis.StackingTensorHomDimension
import Superfusion.Bimod.GradedModule

/-! The total tensor-Hom isomorphism respects the actual Hom grading.
Its inverse preserves degrees by uniqueness of the two homogeneous components. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open CategoryTheory
open scoped TensorProduct
namespace RMod.BrundanEllis.Stacking.Raw
open RMod.Classification Superfusion.Bimod
variable (C : RMod.WeaklyPointedSuperfusion.{0, 0})
variable (X X' Y Y' : LinearCategory C)

/-- The linear tensor operation preserves the convolution grading. -/
theorem tensorHomLinear_grade {a : ZMod 2} {z : (X ⟶ X') ⊗[ℝ] (Y ⟶ Y')}
    (hz : z ∈ tensorGrading (LinearCategory.grade C X X') (LinearCategory.grade C Y Y') a) :
    tensorHomLinear C X X' Y Y' z ∈
      LinearCategory.grade C (C.data.tensorObj X Y) (C.data.tensorObj X' Y') a := by
  refine tensorGrading_induction (LinearCategory.grade C X X') (LinearCategory.grade C Y Y')
    (motive := fun z => tensorHomLinear C X X' Y Y' z ∈
      LinearCategory.grade C (C.data.tensorObj X Y) (C.data.tensorObj X' Y') a) hz ?_ ?_ ?_ ?_
  · intro i j f g hij hf hg
    subst a
    exact C.laws.tensor_grade f g hf hg
  · simp
  · intro x y hx hy
    simpa using Submodule.add_mem _ hx hy
  · intro r x hx
    simpa using Submodule.smul_mem _ r hx

/-- Restrict the specified operation, without choosing a different degree map. -/
def tensorHomGrade (a : ZMod 2) :
    tensorGrading (LinearCategory.grade C X X') (LinearCategory.grade C Y Y') a →ₗ[ℝ]
      LinearCategory.grade C (C.data.tensorObj X Y) (C.data.tensorObj X' Y') a :=
  ((tensorHomLinear C X X' Y Y').domRestrict _).codRestrict _
    (fun z => tensorHomLinear_grade C X X' Y Y' z.property)

/-- A bijective total tensor operation is bijective in every degree. -/
theorem tensorHomGrade_bijective
    (h : Function.Bijective (tensorHomLinear C X X' Y Y')) (a : ZMod 2) :
    Function.Bijective (tensorHomGrade C X X' Y Y' a) := by
  letI := (LinearCategory.grade_isInternal C X X').chooseDecomposition
  letI := (LinearCategory.grade_isInternal C Y Y').chooseDecomposition
  letI := (LinearCategory.grade_isInternal C (C.data.tensorObj X Y)
    (C.data.tensorObj X' Y')).chooseDecomposition
  let e := LinearEquiv.ofBijective (tensorHomLinear C X X' Y Y') h
  constructor
  · intro z z' he
    exact Subtype.ext (h.injective (congrArg Subtype.val he))
  · intro f
    have hf : e.symm f.val ∈
        tensorGrading (LinearCategory.grade C X X') (LinearCategory.grade C Y Y') a :=
      gradedLinearEquiv_symm_mem
        (tensorGrading (LinearCategory.grade C X X') (LinearCategory.grade C Y Y'))
        (LinearCategory.grade C (C.data.tensorObj X Y) (C.data.tensorObj X' Y')) e
        (fun {_ _} hz => tensorHomLinear_grade C X X' Y Y' hz) f.property
    exact ⟨⟨e.symm f.val, hf⟩, Subtype.ext (e.apply_symm_apply f.val)⟩

end RMod.BrundanEllis.Stacking.Raw
