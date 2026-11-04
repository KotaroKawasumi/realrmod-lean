import Mathlib.LinearAlgebra.TensorProduct.Graded.Internal

/-!
# Induction on the folded graded tensor product

The graded tensor product is a type synonym of the ordinary tensor
product with a different multiplication.  This file exposes the
ordinary additive induction principle directly at the folded type, so
clients need not repeatedly unfold and re-fold its carrier.
-/

open scoped TensorProduct

namespace GradedTensorProduct

universe uR uι uA uB

variable {R : Type uR} {ι : Type uι}
variable {A : Type uA} {B : Type uB}
variable [CommSemiring ι] [DecidableEq ι]
variable [CommRing R] [Ring A] [Ring B]
variable [Algebra R A] [Algebra R B]
variable (𝒜 : ι → Submodule R A) (ℬ : ι → Submodule R B)
variable [GradedAlgebra 𝒜] [GradedAlgebra ℬ]

/-- Induction on a folded graded tensor product by pure tensors,
zero, and addition.

This is `TensorProduct.induction_on` transported across
`GradedTensorProduct.of`.  Keeping the result at the folded type avoids
cast markers caused by its distinct multiplication. -/
@[elab_as_elim]
theorem induction_on
    {p : (𝒜 ᵍ⊗[R] ℬ) → Prop}
    (x : 𝒜 ᵍ⊗[R] ℬ)
    (tmul : ∀ (a : A) (b : B), p (a ᵍ⊗ₜ[R] b))
    (zero : p 0)
    (add : ∀ x y, p x → p y → p (x + y)) :
    p x := by
  have key : ∀ t : A ⊗[R] B, p (of R 𝒜 ℬ t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => exact zero
    | tmul a b => exact tmul a b
    | add x y hx hy =>
        rw [map_add]
        exact add _ _ hx hy
  have h := key ((of R 𝒜 ℬ).symm x)
  rwa [symm_of_of] at h

end GradedTensorProduct
