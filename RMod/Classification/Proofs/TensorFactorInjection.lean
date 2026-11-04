import RMod.Classification.Proofs.TensorEndInjection
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Detecting one factor of a tensor

A linear functional taking a nonzero vector to one gives a left inverse
to tensoring with that vector. Combined with tensor-endomorphism
injectivity, this reflects equality after tensoring endomorphisms with
the identity of a nonzero object.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

theorem tensor_right_factor_injective {K A B : Type*} [Field K]
    [AddCommGroup A] [AddCommGroup B] [Module K A] [Module K B]
    {b : B} (hb : b ≠ 0) : Function.Injective (fun a : A => TensorProduct.tmul K a b) := by
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one K hb
  intro a a' h
  have he := congrArg (fun t => TensorProduct.rid K A ((φ.lTensor A) t)) h
  simpa [hφ] using he

theorem tensorEnd_right_id_injective (C : WeaklyPointedSuperfusion.{0, 0})
    (X Y : LinearCategory C) (hY : C.data.id Y ≠ C.data.zero) :
    Function.Injective (fun f : End (C := LinearCategory C) X => C.data.tensorHom f (C.data.id Y)) := by
  have hi : Function.Injective (fun f : End (C := LinearCategory C) X =>
      TensorProduct.tmul ℝ f (1 : End (C := LinearCategory C) Y)) :=
    tensor_right_factor_injective hY
  intro f g h
  apply hi
  apply tensorEndLinear_injective C X Y
  exact h

end RMod.Classification
