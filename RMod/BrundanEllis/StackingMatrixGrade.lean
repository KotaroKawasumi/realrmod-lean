import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Real.Basic

/-! A matrix supported in one parity gives a homogeneous linear map.
This elementary bridge lets finite rational certificates control the real
fusion kernels without trusting an external matrix computation. -/
noncomputable section
set_option autoImplicit false
namespace RMod.BrundanEllis.Stacking

/-- A coordinate vector has degree `d` when its other coordinates vanish. -/
def CoordinateGrade {I : Type*} (p : I → ZMod 2) (d : ZMod 2)
    (v : I → ℝ) : Prop := ∀ i, p i ≠ d → v i = 0

/-- Reading a rational matrix over the reals preserves its support. -/
theorem matrix_grade {I J : Type*} [Fintype I]
    (p : I → ZMod 2) (q : J → ZMod 2) (d : ZMod 2)
    (A : Matrix J I ℚ)
    (hA : ∀ j i, A j i ≠ 0 → q j = p i + d)
    {e : ZMod 2} {v : I → ℝ} (hv : CoordinateGrade p e v) :
    CoordinateGrade q (e + d) ((A.map ((↑) : ℚ → ℝ)).mulVec v) := by
  intro j hj
  apply Finset.sum_eq_zero
  intro i hi
  by_cases h : A j i = 0
  · simp [Matrix.map_apply, h]
  · have hp : p i ≠ e := by
      intro he
      exact hj ((hA j i h).trans (congrArg (fun z => z + d) he))
    simp [hv i hp]

/-- Two explicitly supplied rational inverse matrices give a real linear equivalence. -/
def matrixEquivOfInverse {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (A : Matrix J I ℚ) (B : Matrix I J ℚ)
    (hBA : B * A = 1) (hAB : A * B = 1) :
    (I → ℝ) ≃ₗ[ℝ] (J → ℝ) where
  toLinearMap := (A.map ((↑) : ℚ → ℝ)).mulVecLin
  invFun := (B.map ((↑) : ℚ → ℝ)).mulVec
  left_inv v := by
    change (B.map ((↑) : ℚ → ℝ)).mulVec ((A.map ((↑) : ℚ → ℝ)).mulVec v) = v
    rw [Matrix.mulVec_mulVec]
    have h : B.map ((↑) : ℚ → ℝ) * A.map ((↑) : ℚ → ℝ) = 1 := by
      ext i j
      have h := congrArg ((↑) : ℚ → ℝ) (congrFun (congrFun hBA i) j)
      simpa [Matrix.mul_apply, Matrix.one_apply, apply_ite] using h
    rw [h, Matrix.one_mulVec]
  right_inv v := by
    change (A.map ((↑) : ℚ → ℝ)).mulVec ((B.map ((↑) : ℚ → ℝ)).mulVec v) = v
    rw [Matrix.mulVec_mulVec]
    have h : A.map ((↑) : ℚ → ℝ) * B.map ((↑) : ℚ → ℝ) = 1 := by
      ext i j
      have h := congrArg ((↑) : ℚ → ℝ) (congrFun (congrFun hAB i) j)
      simpa [Matrix.mul_apply, Matrix.one_apply, apply_ite] using h
    rw [h, Matrix.one_mulVec]

/-- A checked rational intertwining identity remains valid on all real vectors. -/
theorem matrix_intertwiner {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix J I ℚ) (L : Matrix I I ℚ) (R : Matrix J J ℚ) (q : ℚ)
    (h : A * L = q • (R * A)) (v : I → ℝ) :
    (A.map ((↑) : ℚ → ℝ)).mulVec ((L.map ((↑) : ℚ → ℝ)).mulVec v) =
      (q : ℝ) • (R.map ((↑) : ℚ → ℝ)).mulVec ((A.map ((↑) : ℚ → ℝ)).mulVec v) := by
  have h' : A.map ((↑) : ℚ → ℝ) * L.map ((↑) : ℚ → ℝ) =
      (q : ℝ) • (R.map ((↑) : ℚ → ℝ) * A.map ((↑) : ℚ → ℝ)) := by
    ext i j
    have hentry := congrArg ((↑) : ℚ → ℝ) (congrFun (congrFun h i) j)
    simpa [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul] using hentry
  rw [Matrix.mulVec_mulVec, h', Matrix.smul_mulVec, Matrix.mulVec_mulVec]

/-- To compare linear maps on a homogeneous vector, only basis vectors in
that degree need be compared. -/
theorem coordinateGrade_ext {I : Type*} [Fintype I] [DecidableEq I]
    {M : Type*} [AddCommGroup M] [Module ℝ M]
    (p : I → ZMod 2) (d : ZMod 2) (F H : (I → ℝ) →ₗ[ℝ] M)
    (h : ∀ i, p i = d → F (Pi.single i 1) = H (Pi.single i 1))
    {v : I → ℝ} (hv : CoordinateGrade p d v) : F v = H v := by
  have hvsum : v = ∑ i, v i • Pi.single i 1 := by
    funext j
    simp [Pi.single_apply]
  rw [hvsum, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_smul, map_smul]
  by_cases he : p i = d
  · rw [h i he]
  · rw [hv i he]
    simp

end RMod.BrundanEllis.Stacking
