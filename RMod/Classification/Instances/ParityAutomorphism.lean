import Superfusion.Super.ParityInvolution
import RMod.Classification.Proofs.Parity

/-!
# Powers of the parity automorphism

This is the existing algebra parity involution, raised to a parity's
natural representative. It corrects conjugation by an odd object
isomorphism when forming a signed natural comparison.
-/

set_option autoImplicit false

namespace RMod.Classification

variable {A : Type*} [Ring A] [Algebra ℝ A]
  (𝒜 : ZMod 2 → Submodule ℝ A) [GradedAlgebra 𝒜]

noncomputable def parityAutomorphism (a : ZMod 2) : A ≃ₐ[ℝ] A :=
  (Superfusion.parityInvolution 𝒜) ^ a.val

end RMod.Classification
