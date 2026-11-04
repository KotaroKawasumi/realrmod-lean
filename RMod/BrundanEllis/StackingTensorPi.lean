import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.Data.Real.Basic

/-! Tensoring two finite families is the family indexed by pairs. These
linear equivalences retain the coordinatewise pure-tensor formula. -/
noncomputable section
set_option autoImplicit false
open scoped TensorProduct
namespace RMod.BrundanEllis.Stacking.Linear
variable {I J : Type} [Fintype I] [Fintype J]
  (V : I → Type) (W : J → Type)
  [∀ i, AddCommGroup (V i)] [∀ i, Module ℝ (V i)]
  [∀ j, AddCommGroup (W j)] [∀ j, Module ℝ (W j)]

/-- Reindex an iterated family by the product of its two index types. -/
def uncurry (Z : I → J → Type) [∀ i j, AddCommGroup (Z i j)] [∀ i j, Module ℝ (Z i j)] :
    (∀ i j, Z i j) ≃ₗ[ℝ] (∀ ij : I × J, Z ij.1 ij.2) where
  toFun f ij := f ij.1 ij.2
  invFun f i j := f (i, j)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The usual finite-product distribution of tensor products, on both sides. -/
def tensorPiEquiv : ((∀ i, V i) ⊗[ℝ] (∀ j, W j)) ≃ₗ[ℝ]
    (∀ ij : I × J, V ij.1 ⊗[ℝ] W ij.2) := by
  classical
  exact (TensorProduct.piLeft ℝ (∀ j, W j) V).trans
    ((LinearEquiv.piCongrRight fun i => TensorProduct.piRight ℝ ℝ (V i) W).trans
      (uncurry fun i j => V i ⊗[ℝ] W j))

theorem tensorPiEquiv_tmul (f : ∀ i, V i) (g : ∀ j, W j) (ij : I × J) :
    tensorPiEquiv V W (f ⊗ₜ[ℝ] g) ij = f ij.1 ⊗ₜ[ℝ] g ij.2 := by
  classical
  simp [tensorPiEquiv, uncurry, TensorProduct.piRightHom_tmul]

end RMod.BrundanEllis.Stacking.Linear
