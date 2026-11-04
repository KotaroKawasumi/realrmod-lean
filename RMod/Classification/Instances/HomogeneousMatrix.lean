import RMod.Classification.Proofs.HomogeneousSums
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Endomorphism matrices for a homogeneous sum

The row index is the output summand and the column index the input
summand. With this convention categorical endomorphism multiplication
agrees with ordinary matrix multiplication, without an opposite algebra.
-/

set_option autoImplicit false

namespace RMod.Classification.HomogeneousSum

open CategoryTheory CategoryTheory.Preadditive

attribute [local implicit_reducible] CategoryTheory.End Matrix

variable {C : WeaklyPointedSuperfusion.{0, 0}}
  {X Y : LinearCategory C} {n : ℕ}
  (d : HomogeneousSum C.data X Y n)

/-- Taking all matrix components, using Mathlib's endomorphism algebra. -/
def toMatrix (f : End Y) : Matrix (Fin n) (Fin n) (End X) :=
  fun i j => d.data.inclusion j ≫ f ≫ d.data.projection i

/-- Extend a coefficient matrix by the chosen inclusions and projections. -/
def fromMatrix (m : Matrix (Fin n) (Fin n) (End X)) : End Y :=
  ∑ j, ∑ i, d.data.projection j ≫ m i j ≫ d.data.inclusion i

theorem total : ∑ i, d.data.projection i ≫ d.data.inclusion i = 𝟙 Y := by
  have h := d.laws.total
  rw [LinearCategory.finSum_eq_sum C (X := Y) (Y := Y)] at h
  exact h

theorem inclusion_projection (i j : Fin n) :
    d.data.inclusion i ≫ d.data.projection j = if i = j then 𝟙 X else 0 := by
  split_ifs with h
  · subst j
    exact d.laws.diagonal i
  · exact d.laws.off_diagonal i j h

@[simp]
theorem toMatrix_fromMatrix (m : Matrix (Fin n) (Fin n) (End X)) :
    toMatrix d (fromMatrix d m) = m := by
  ext i j
  change d.data.inclusion j ≫
    (∑ k, ∑ l, d.data.projection k ≫ m l k ≫ d.data.inclusion l : Y ⟶ Y) ≫
      d.data.projection i = m i j
  simp only [comp_sum, sum_comp]
  have hterm (k l : Fin n) :
      d.data.inclusion j ≫ (d.data.projection k ≫ m l k ≫ d.data.inclusion l) ≫
          d.data.projection i =
        (d.data.inclusion j ≫ d.data.projection k) ≫ m l k ≫
          (d.data.inclusion l ≫ d.data.projection i) := by simp only [Category.assoc]
  conv_lhs =>
    arg 2
    ext k
    arg 2
    ext l
    rw [hterm k l, inclusion_projection, inclusion_projection]
  simp [ite_comp, comp_ite]

@[simp]
theorem fromMatrix_toMatrix (f : End Y) : fromMatrix d (toMatrix d f) = f := by
  have hterm (j i : Fin n) :
      d.data.projection j ≫ (d.data.inclusion j ≫ f ≫ d.data.projection i) ≫
          d.data.inclusion i =
        (d.data.projection j ≫ d.data.inclusion j) ≫ f ≫
          (d.data.projection i ≫ d.data.inclusion i) := by simp only [Category.assoc]
  change (∑ j, ∑ i, d.data.projection j ≫
    (d.data.inclusion j ≫ f ≫ d.data.projection i) ≫ d.data.inclusion i : Y ⟶ Y) = f
  simp only [hterm]
  simp only [← comp_sum (C := LinearCategory C), total, Category.comp_id]
  rw [← sum_comp (C := LinearCategory C), total, Category.id_comp]

theorem toMatrix_one : toMatrix d (1 : End Y) = 1 := by
  ext i j
  change d.data.inclusion j ≫ 𝟙 Y ≫ d.data.projection i = _
  rw [Category.id_comp, inclusion_projection, Matrix.one_apply]
  change (if j = i then (1 : End X) else 0) = if i = j then 1 else 0
  simp only [eq_comm]

theorem toMatrix_mul (f g : End Y) : toMatrix d (f * g) = toMatrix d f * toMatrix d g := by
  ext i j
  change d.data.inclusion j ≫ (g ≫ f) ≫ d.data.projection i = _
  rw [Matrix.mul_apply]
  change _ = ∑ k, (d.data.inclusion j ≫ g ≫ d.data.projection k) ≫
    (d.data.inclusion k ≫ f ≫ d.data.projection i)
  simp only [Category.assoc]
  have hterm (k : Fin n) :
      d.data.inclusion j ≫ g ≫ d.data.projection k ≫ d.data.inclusion k ≫
          f ≫ d.data.projection i =
        d.data.inclusion j ≫ g ≫ (d.data.projection k ≫ d.data.inclusion k) ≫
          f ≫ d.data.projection i := by simp only [Category.assoc]
  simp only [hterm, ← comp_sum (C := LinearCategory C), ← sum_comp (C := LinearCategory C), total, Category.id_comp]

/-- The actual algebra equivalence of endomorphisms and matrices. -/
def matrixAlgEquiv : End Y ≃ₐ[ℝ] Matrix (Fin n) (Fin n) (End X) :=
  AlgEquiv.ofLinearEquiv
    { toFun := toMatrix d
      invFun := fromMatrix d
      left_inv := fromMatrix_toMatrix d
      right_inv := toMatrix_fromMatrix d
      map_add' := by
        intro f g
        ext i j
        change C.data.comp (d.data.inclusion j) (C.data.comp (C.data.add f g)
          (d.data.projection i)) = C.data.add _ _
        rw [C.laws.add_comp, C.laws.comp_add]
        rfl
      map_smul' := by
        intro r f
        ext i j
        change C.data.comp (d.data.inclusion j) (C.data.comp (C.data.smul r f)
          (d.data.projection i)) = C.data.smul r _
        rw [C.laws.smul_comp, C.laws.comp_smul]
        rfl }
    (toMatrix_one d) (toMatrix_mul d)

end RMod.Classification.HomogeneousSum
