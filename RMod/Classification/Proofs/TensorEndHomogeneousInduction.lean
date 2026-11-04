import RMod.Classification.Instances.TensorEndEquivalence

/-!
# Homogeneous tensor endomorphisms are spanned by homogeneous pure tensors

The tensor-endomorphism equivalence identifies each graded piece with
the span defining the graded tensor product. This transfers the existing
graded span induction principle to actual categorical endomorphisms.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory Superfusion Superfusion.Category GradedTensorProduct
open scoped TensorProduct

attribute [local implicit_reducible] CategoryTheory.End
  Superfusion.Category.endSuperAlgebra Superfusion.Category.endGrading

theorem tensorEnd_homogeneous_induction (C : WeaklyPointedSuperfusion.{0, 0})
    (S T : LinearCategory C) (hT : C.data.IsSimple T) {a : ZMod 2}
    {P : @End (LinearCategory C) _ (C.data.tensorObj S T) → Prop}
    (k : @End (LinearCategory C) _ (C.data.tensorObj S T)) (hk : C.data.IsHomogeneous a k)
    (htensor : ∀ (b c : ZMod 2) (f : End S) (g : End T), b + c = a →
      C.data.IsHomogeneous b f → C.data.IsHomogeneous c g → P (C.data.tensorHom f g))
    (hzero : P 0) (hadd : ∀ f g, P f → P g → P (f + g))
    (hsmul : ∀ (r : ℝ) f, P f → P (r • f)) : P k := by
  let e := tensorEndSuperEquiv C S T hT
  obtain ⟨z, rfl⟩ := e.toAlgEquiv.surjective k
  have hz : z ∈ tensorGrading (endGrading (K := ℝ) S) (endGrading (K := ℝ) T) a :=
    (mem_iff_map_mem _ _ e.toAlgEquiv e.map_grading).mpr hk
  refine tensorGrading_induction (endGrading (K := ℝ) S) (endGrading (K := ℝ) T) hz
    (p := fun w => P (tensorEndAlgHom C S T w)) ?_ ?_ ?_ ?_
  · intro b c f g hbc hf hg
    rw [tensorEndAlgHom_tmul]
    exact htensor b c f g hbc hf hg
  · rw [map_zero]
    exact hzero
  · intro f g hf hg
    rw [map_add]
    exact hadd _ _ hf hg
  · intro r f hf
    rw [map_smul]
    exact hsmul _ _ hf

end RMod.Classification
