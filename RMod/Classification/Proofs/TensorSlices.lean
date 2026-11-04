import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Detecting a tensor-product kernel by slices

If every linear functional on the first factor can be realized as a slice
after a bilinear map, its tensor-product lift is injective. Mathlib's
Finsupp coordinates for an arbitrary basis detect every tensor coefficient;
no finite-dimensional hypothesis or new coordinate structure is needed.
-/

set_option autoImplicit false

namespace RMod.Classification

variable {K A B E : Type*} [Field K]
  [AddCommGroup A] [AddCommGroup B] [AddCommGroup E]
  [Module K A] [Module K B] [Module K E]

theorem tensor_lift_injective_of_slices (b : A →ₗ[K] B →ₗ[K] E)
    (hslice : ∀ φ : Module.Dual K A, ∃ S : E →ₗ[K] B,
      ∀ a c, S (b a c) = (φ a) • c) :
    Function.Injective (TensorProduct.lift b) := by
  classical
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro u hu
  let basis := Module.Free.chooseBasis K A
  apply (TensorProduct.equivFinsuppOfBasisLeft (N := B) basis).injective
  ext i
  rw [map_zero, Finsupp.zero_apply, TensorProduct.equivFinsuppOfBasisLeft_apply]
  obtain ⟨S, hS⟩ := hslice (basis.coord i)
  have he : S.comp (TensorProduct.lift b) =
      (TensorProduct.lid K B).toLinearMap.comp ((basis.coord i).rTensor B) := by
    ext a c
    simpa using hS a c
  have h := DFunLike.congr_fun he u
  change S (TensorProduct.lift b u) = TensorProduct.lid K B ((basis.coord i).rTensor B u) at h
  rw [hu, map_zero] at h
  exact h.symm

end RMod.Classification
