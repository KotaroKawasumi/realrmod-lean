import RMod.BrundanEllis.Foundation

/-! The change between chronological and original tensor conventions is an
involution on the graded tensor source, including the odd-odd summand. -/
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.MonoidalCategory GradedObject.Monoidal
open scoped TensorProduct
namespace RMod.BrundanEllis.Stacking.Graded

def tensorSign (X Y : SuperVec) (a : ZMod 2) : (X ⊗ Y) a ⟶ (X ⊗ Y) a :=
  tensorObjDesc fun i j h => ((-1 : ℝ) ^ (i * j).val) • ιTensorObj X Y i j a h

theorem tensorSign_tmul (X Y : SuperVec) (i j a : ZMod 2) (h : i + j = a)
    (x : X i) (y : Y j) :
    tensorSign X Y a (ιTensorObj X Y i j a h (x ⊗ₜ[ℝ] y)) =
      ((-1 : ℝ) ^ (i * j).val) • ιTensorObj X Y i j a h (x ⊗ₜ[ℝ] y) := by
  exact congrArg (fun q => q (x ⊗ₜ[ℝ] y))
    (ι_tensorObjDesc (X₁ := X) (X₂ := Y)
      (fun i j h => ((-1 : ℝ) ^ (i * j).val) • ιTensorObj X Y i j a h) i j h)

theorem tensorSign_involutive (X Y : SuperVec) (a : ZMod 2) :
    Function.Involutive (tensorSign X Y a) := by
  have he : tensorSign X Y a ≫ tensorSign X Y a = 𝟙 _ := by
    apply tensorObj_ext
    intro i j h
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro x y
    change tensorSign X Y a (tensorSign X Y a
      (ιTensorObj X Y i j a h (x ⊗ₜ[ℝ] y))) =
        ιTensorObj X Y i j a h (x ⊗ₜ[ℝ] y)
    rw [tensorSign_tmul]
    change (tensorSign X Y a).hom (_ • _) = _
    rw [map_smul, tensorSign_tmul, smul_smul, ← mul_pow, neg_mul_neg, one_mul, one_pow, one_smul]
  intro x
  exact congrArg (fun q => q x) he

def tensorSignEquiv (X Y : SuperVec) (a : ZMod 2) : (X ⊗ Y) a ≃ₗ[ℝ] (X ⊗ Y) a :=
  LinearEquiv.ofBijective (tensorSign X Y a).hom (tensorSign_involutive X Y a).bijective

end RMod.BrundanEllis.Stacking.Graded
