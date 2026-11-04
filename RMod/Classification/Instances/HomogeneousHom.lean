import RMod.Classification.Instances.HomogeneousMatrix
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Hom coordinates for homogeneous sums

Composition with the projections identifies Hom(U,Y) with one copy of
Hom(U,X) per summand of a homogeneous sum of X. This is an equivalence of
the complete real Hom spaces; its inverse is the finite sum of the given
inclusions. No choice of bases or simplicity assumption is involved.
-/

set_option autoImplicit false

namespace RMod.Classification.HomogeneousSum

open CategoryTheory CategoryTheory.Preadditive

variable {C : WeaklyPointedSuperfusion.{0, 0}}
  {X Y : LinearCategory C} {n : ℕ} (d : HomogeneousSum C.data X Y n)

def homToEquiv (U : LinearCategory C) : (U ⟶ Y) ≃ₗ[ℝ] (Fin n → (U ⟶ X)) where
  toFun f i := f ≫ d.data.projection i
  invFun f := ∑ i, f i ≫ d.data.inclusion i
  left_inv f := by
    simp only [Category.assoc, ← comp_sum, d.total, Category.comp_id]
  right_inv f := by
    ext j
    simp only [sum_comp, Category.assoc, d.inclusion_projection]
    simp [comp_ite]
  map_add' f g := by
    ext i
    exact C.laws.add_comp f g (d.data.projection i)
  map_smul' r f := by
    ext i
    exact C.laws.smul_comp r f (d.data.projection i)

include d in
theorem finrank_homTo (U : LinearCategory C) :
    Module.finrank ℝ (U ⟶ Y) = n * Module.finrank ℝ (U ⟶ X) := by
  calc
    _ = Module.finrank ℝ (Fin n → (U ⟶ X)) :=
      LinearEquiv.finrank_eq (d.homToEquiv (C := C) U)
    _ = n * Module.finrank ℝ (U ⟶ X) := by
      rw [Module.finrank_pi_fintype]
      simp

end RMod.Classification.HomogeneousSum
