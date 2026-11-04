import RMod.Classification.Instances.TensorHomBilinear
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Tensoring finite sums of morphisms

The supplied finite sum operation agrees with Mathlib's finite sum.
The two linear maps obtained from the tensor bilinear map therefore
preserve these sums, including when the maps are not homogeneous.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification

open CategoryTheory

variable (C : WeaklyPointedSuperfusion.{u, v}) {X X' Y Y' : LinearCategory C}

theorem finSum_finProd (n m : ℕ) (f : Fin n × Fin m → (X ⟶ X')) :
    C.data.finSum (n * m) (fun k => f (finProdFinEquiv.symm k)) =
      C.data.finSum n (fun i => C.data.finSum m (fun j => f (i, j))) := by
  simp only [LinearCategory.finSum_eq_sum C]
  rw [Equiv.sum_comp, Fintype.sum_prod_type]

theorem tensor_finSum_left (n : ℕ) (f : Fin n → (X ⟶ X')) (g : Y ⟶ Y') :
    C.data.tensorHom (C.data.finSum n f) g =
      C.data.finSum n (fun i => C.data.tensorHom (f i) g) := by
  rw [LinearCategory.finSum_eq_sum C, LinearCategory.finSum_eq_sum C]
  exact map_sum ((tensorHomBilinear C X X' Y Y').flip g) f Finset.univ

theorem tensor_finSum_right (n : ℕ) (f : X ⟶ X') (g : Fin n → (Y ⟶ Y')) :
    C.data.tensorHom f (C.data.finSum n g) =
      C.data.finSum n (fun i => C.data.tensorHom f (g i)) := by
  rw [LinearCategory.finSum_eq_sum C, LinearCategory.finSum_eq_sum C]
  exact map_sum (tensorHomBilinear C X X' Y Y' f) g Finset.univ

end RMod.Classification
