import RMod.BrundanEllis.Foundation
import Superfusion.Bimod.GradedModule

/-! A tensor product of graded Hom objects realizes the usual homogeneous
layer of the tensor product of their total vector spaces. The explicit
projection proves injectivity; the defining homogeneous span proves surjectivity. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open CategoryTheory CategoryTheory.MonoidalCategory GradedObject.Monoidal
open scoped TensorProduct
namespace RMod.BrundanEllis.Stacking.Graded
variable {V W : Type} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
  (v : ZMod 2 → Submodule ℝ V) (w : ZMod 2 → Submodule ℝ W)
  [DirectSum.Decomposition v] [DirectSum.Decomposition w]

abbrev object (v : ZMod 2 → Submodule ℝ V) : SuperVec := fun a => ModuleCat.of ℝ (v a)

def projectInto (a : ZMod 2) : V →ₗ[ℝ] (v a) :=
  LinearMap.codRestrict (v a) (Superfusion.Bimod.modProj v a) (Superfusion.Bimod.modProj_mem v a)

@[simp] theorem projectInto_same (a : ZMod 2) (x : v a) : projectInto v a x.val = x :=
  Subtype.ext (Superfusion.Bimod.modProj_of_mem v x.property)

@[simp] theorem projectInto_ne {a b : ZMod 2} (h : a ≠ b) (x : v a) :
    projectInto v b x.val = 0 :=
  Subtype.ext (Superfusion.Bimod.modProj_of_mem_ne v x.property h)

/-- Inclusion of each homogeneous tensor into the total tensor product. -/
def includeTensor (a : ZMod 2) : (object v ⊗ object w) a ⟶ ModuleCat.of ℝ (V ⊗[ℝ] W) :=
  tensorObjDesc fun i j _ => ModuleCat.ofHom (TensorProduct.map (v i).subtype (w j).subtype)

theorem includeTensor_tmul (i j a : ZMod 2) (h : i + j = a) (x : v i) (y : w j) :
    includeTensor v w a (ιTensorObj (object v) (object w) i j a h (x ⊗ₜ[ℝ] y)) =
      x.val ⊗ₜ[ℝ] y.val := by
  exact congrArg (fun q => q (x ⊗ₜ[ℝ] y))
    (ι_tensorObjDesc (X₁ := object v) (X₂ := object w) (fun i j _ => ModuleCat.ofHom (TensorProduct.map (v i).subtype (w j).subtype)) i j h)

/-- Keep precisely the two summands with total degree a. -/
def projectTensor (a : ZMod 2) : V ⊗[ℝ] W →ₗ[ℝ] (object v ⊗ object w) a :=
  (ιTensorObj (object v) (object w) 0 a a (zero_add a)).hom.comp
      (TensorProduct.map (projectInto v 0) (projectInto w a)) +
    (ιTensorObj (object v) (object w) 1 (a + 1) a (by
      have h : (1 : ZMod 2) + 1 = 0 := rfl
      rw [add_left_comm, h, add_zero])).hom.comp
      (TensorProduct.map (projectInto v 1) (projectInto w (a + 1)))

/-- The projection recovers each included pure tensor of the specified degree. -/
theorem projectTensor_tmul (i j a : ZMod 2) (h : i + j = a) (x : v i) (y : w j) :
    projectTensor v w a (x.val ⊗ₜ[ℝ] y.val) =
      ιTensorObj (object v) (object w) i j a h (x ⊗ₜ[ℝ] y) := by
  change (ιTensorObj (object v) (object w) 0 a a (zero_add a)).hom
      (projectInto v 0 x.val ⊗ₜ[ℝ] projectInto w a y.val) +
      (ιTensorObj (object v) (object w) 1 (a + 1) a _).hom
      (projectInto v 1 x.val ⊗ₜ[ℝ] projectInto w (a + 1) y.val) = _
  subst a
  rcases Superfusion.zmod2_cases i with rfl | rfl <;>
    rcases Superfusion.zmod2_cases j with rfl | rfl <;>
    simp only [add_zero, zero_add, show (1 : ZMod 2) + 1 = 0 from rfl,
      projectInto_same, projectInto_ne v zero_ne_one, projectInto_ne v one_ne_zero,
      projectInto_ne w zero_ne_one, projectInto_ne w one_ne_zero,
      TensorProduct.zero_tmul, TensorProduct.tmul_zero, map_zero, add_zero, zero_add] <;> rfl


/-- No relations beyond tensor bilinearity are introduced by the graded coproduct. -/
theorem includeTensor_injective (a : ZMod 2) : Function.Injective (includeTensor v w a) := by
  have he : includeTensor v w a ≫ ModuleCat.ofHom (projectTensor v w a) = 𝟙 _ := by
    apply tensorObj_ext
    intro i j h
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro x y
    change projectTensor v w a (includeTensor v w a
      (ιTensorObj (object v) (object w) i j a h (x ⊗ₜ[ℝ] y))) =
      ιTensorObj (object v) (object w) i j a h (x ⊗ₜ[ℝ] y)
    rw [includeTensor_tmul, projectTensor_tmul]
  have hleft : Function.LeftInverse (projectTensor v w a) (includeTensor v w a) := by
    intro x
    exact congrArg (fun q => q x) he
  exact hleft.injective

/-- The range is exactly the module tensor grading used by the existing library. -/
theorem includeTensor_range (a : ZMod 2) :
    LinearMap.range (includeTensor v w a).hom = Superfusion.Bimod.tensorGrading v w a := by
  apply le_antisymm
  · intro z hz
    obtain ⟨x, rfl⟩ := hz
    have h : ∀ x, includeTensor v w a x ∈ Superfusion.Bimod.tensorGrading v w a := by
      let F : (object v ⊗ object w) a ⟶ ModuleCat.of ℝ (Superfusion.Bimod.tensorGrading v w a) :=
        tensorObjDesc fun i j hij => ModuleCat.ofHom
          ((TensorProduct.map (v i).subtype (w j).subtype).codRestrict _ (by
            intro u
            induction u using TensorProduct.induction_on with
            | zero => simp
            | tmul vx wy =>
                subst a
                exact Superfusion.Bimod.tmul_mem_tensorGrading v w vx.property wy.property
            | add u₁ u₂ hu₁ hu₂ => simpa using Submodule.add_mem _ hu₁ hu₂))
      have hf : F ≫ ModuleCat.ofHom (Superfusion.Bimod.tensorGrading v w a).subtype =
          includeTensor v w a := by
        apply tensorObj_ext
        intro i j hij
        dsimp only [F, includeTensor]
        rw [← Category.assoc, ι_tensorObjDesc, ι_tensorObjDesc]
        rfl
      intro x
      rw [← hf]
      exact (F x).property
    exact h x
  · apply Submodule.span_le.mpr
    rintro z ⟨i, j, x, y, hij, hx, hy, rfl⟩
    exact ⟨ιTensorObj (object v) (object w) i j a hij (⟨x, hx⟩ ⊗ₜ[ℝ] ⟨y, hy⟩),
      includeTensor_tmul v w i j a hij ⟨x, hx⟩ ⟨y, hy⟩⟩

/-- The graded tensor component is the specified submodule of the total tensor. -/
def includeTensorEquiv (a : ZMod 2) : (object v ⊗ object w) a ≃ₗ[ℝ]
    Superfusion.Bimod.tensorGrading v w a :=
  (LinearEquiv.ofInjective (includeTensor v w a).hom (includeTensor_injective v w a)).trans
    (LinearEquiv.ofEq _ _ (includeTensor_range v w a))

theorem includeTensorEquiv_val (a : ZMod 2) (x : (object v ⊗ object w) a) :
    (includeTensorEquiv v w a x).val = includeTensor v w a x := rfl

end RMod.BrundanEllis.Stacking.Graded
