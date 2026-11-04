import RMod.Classification.Instances.TensorEndAlgebra
import RMod.Classification.Proofs.TensorFactorInjection
import RMod.Classification.Proofs.DualProductEnd
import RMod.Classification.Proofs.TensorNonvanishing

/-!
# Detecting even central endomorphisms on the dual product

An even central endomorphism remains central after tensoring with an
identity whenever the tensor-endomorphism map is surjective. For the
weak-inverse dual product, that surjectivity follows from the two dual
adjunctions and its matrix dimension. Its ordinary matrix center consists
of real scalars, and tensor injectivity reflects this scalar identity.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

variable (C : WeaklyPointedSuperfusion.{0, 0})

attribute [local implicit_reducible] CategoryTheory.End
  tensorRightData tensorRightSuperfunctor Superfunctor.toFunctor

theorem tensor_even_central (X Y : LinearCategory C) (z : End X)
    (hz : C.data.IsHomogeneous 0 z) (hc : z ∈ Subalgebra.center ℝ (End X))
    (hsurj : Function.Surjective (tensorEndLinear C X Y)) :
    (tensorRightSuperfunctor C Y).endAlgHom X z ∈
      Subalgebra.center ℝ (End (C := LinearCategory C) (C.data.tensorObj X Y)) := by
  apply Subalgebra.mem_center_iff.mpr
  intro T
  obtain ⟨t, rfl⟩ := hsurj T
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero, zero_mul, mul_zero]
  | add s t hs ht => simp only [map_add, add_mul, mul_add, hs, ht]
  | tmul f g =>
    change C.data.comp (C.data.tensorHom z (C.data.id Y)) (C.data.tensorHom f g) =
      C.data.comp (C.data.tensorHom f g) (C.data.tensorHom z (C.data.id Y))
    rw [interchange_first_even C.laws _ _ _ _ hz,
      interchange_second_even C.laws _ _ _ _ (C.laws.id_even Y),
      C.laws.id_comp, C.laws.comp_id]
    exact congrArg (fun w => C.data.tensorHom w g) ((Subalgebra.mem_center_iff.mp hc) f)

theorem even_central_eq_scalar_of_weaklyInvertible (X : LinearCategory C)
    (hX : C.data.id X ≠ C.data.zero) (hweak : C.data.IsWeaklyInvertible X)
    (z : End X) (hz : C.data.IsHomogeneous 0 z) (hc : z ∈ Subalgebra.center ℝ (End X)) :
    ∃ r : ℝ, z = r • (1 : End X) := by
  obtain ⟨Y, hp, p, q, _, hm⟩ := hweak
  obtain ⟨pair⟩ := (hasExactPairing_iff C X Y).mp hp
  obtain ⟨d⟩ := exists_homogeneousSum_of_superMultiplicity C hm
  have hY : C.data.id Y ≠ C.data.zero := by
    intro he
    exact pair.eval_ne_zero hX
      (hom_eq_zero_of_source C.laws (tensor_id_zero_left C.laws he X) pair.data.eval)
  letI : Algebra.IsCentral ℝ (End (C := LinearCategory C) (C.data.tensorObj X Y)) :=
    d.unit_end_isCentral (C := C)
  have hh := tensor_even_central C X Y z hz hc (pair.tensorEnd_bijective_of_unit_sum d).surjective
  obtain ⟨r, hr⟩ := (Algebra.IsCentral.mem_center_iff ℝ).mp hh
  refine ⟨r, tensorEnd_right_id_injective C X Y hY ?_⟩
  change C.data.tensorHom z (C.data.id Y) =
    C.data.tensorHom (C.data.smul r (C.data.id X)) (C.data.id Y)
  rw [C.laws.tensor_smul_left, C.laws.tensor_id]
  exact hr.trans (Algebra.algebraMap_eq_smul_one r)

end RMod.Classification
