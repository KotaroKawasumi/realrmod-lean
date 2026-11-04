import RMod.Classification.Instances.ParityAutomorphism
import Superfusion.Super.SkolemNoether

/-!
# The homogeneous action of the parity automorphism

On degree b the a-th parity automorphism is multiplication by
(-1)^(ab). In particular it preserves every homogeneous subspace.
-/

set_option autoImplicit false

namespace RMod.Classification

open Superfusion

variable {A : Type*} [Ring A] [Algebra ℝ A]
  (𝒜 : ZMod 2 → Submodule ℝ A) [GradedAlgebra 𝒜]

theorem parityAutomorphism_of_mem (a : ZMod 2) {b : ZMod 2} {f : A} (hf : f ∈ 𝒜 b) :
    parityAutomorphism 𝒜 a f = ((-1 : ℝ) ^ (a * b).val) • f := by
  rcases parity_cases a with rfl | rfl
  · simp [parityAutomorphism]
  · rcases parity_cases b with rfl | rfl
    · simp only [parityAutomorphism, ZMod.val_one, pow_one, one_mul, ZMod.val_zero,
        pow_zero, one_smul]
      change parityMap 𝒜 f = f
      exact parityMap_of_mem_zero 𝒜 hf
    · simp only [parityAutomorphism, ZMod.val_one, pow_one, one_mul, neg_one_smul]
      change parityMap 𝒜 f = -f
      exact parityMap_of_mem_one 𝒜 hf

theorem parityAutomorphism_homogeneous (a : ZMod 2) :
    IsHomogeneousHom 𝒜 𝒜 (parityAutomorphism 𝒜 a).toAlgHom := by
  intro b f hf
  change parityAutomorphism 𝒜 a f ∈ 𝒜 b
  rw [parityAutomorphism_of_mem 𝒜 a hf]
  exact (𝒜 b).smul_mem _ hf

end RMod.Classification
