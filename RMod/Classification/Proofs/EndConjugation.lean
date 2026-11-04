import RMod.Classification.Instances.EndConjugation
import RMod.Classification.Proofs.Grading

/-!
# Homogeneous object conjugation preserves endomorphism degree

Both directions of a homogeneous isomorphism have the same parity.
Their two contributions cancel in characteristic two of the grading
group, so conjugation preserves the degree of every endomorphism.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

attribute [local implicit_reducible] CategoryTheory.End

variable (C : WeaklyPointedSuperfusion.{0, 0}) {X Y : LinearCategory C}

theorem endConjugation_grade (e : X ≅ Y) {a b : ZMod 2}
    (he : C.data.IsHomogeneous a e.hom) (f : End X) (hf : C.data.IsHomogeneous b f) :
    C.data.IsHomogeneous b (endConjugation e f) := by
  have hi := homogeneous_inverse C.laws e.hom e.inv e.hom_inv_id e.inv_hom_id he
  have h := C.laws.comp_grade _ _ hi (C.laws.comp_grade _ _ hf he)
  have hab : a + (b + a) = b := by
    rw [add_left_comm, CharTwo.add_self_eq_zero, add_zero]
  rw [hab] at h
  exact h

end RMod.Classification
