import RMod.Hierarchy.Abstract.Supercategory
import Mathlib.Tactic.Abel
import RMod.Classification.Proofs.Parity

/-!
# Composition on total Hom spaces

The finite convolution combines the even and odd components. Its linearity
comes directly from tensor products and the specified enriched composition.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Category
open GradedObject.Monoidal
open scoped BigOperators TensorProduct
namespace RMod.Legacy


def tComp (d : SupercategoryData) {X Y Z : d.Obj}
    (f : THom d X Y) (g : THom d Y Z) : THom d X Z := fun a =>
  ∑ i : ZMod 2, d.comp X Y Z a
    (GradedObject.Monoidal.ιTensorObj (d.Hom X Y) (d.Hom Y Z)
      i (a - i) a (by abel) (f i ⊗ₜ[ℝ] g (a - i)))

theorem tComp_add_left (d : SupercategoryData) {X Y Z : d.Obj}
    (f g : THom d X Y) (h : THom d Y Z) :
    tComp d (f + g) h = tComp d f h + tComp d g h := by
  funext a
  simp [tComp, TensorProduct.add_tmul, map_add, Finset.sum_add_distrib]

theorem tComp_add_right (d : SupercategoryData) {X Y Z : d.Obj}
    (f : THom d X Y) (g h : THom d Y Z) :
    tComp d f (g + h) = tComp d f g + tComp d f h := by
  funext a
  simp [tComp, TensorProduct.tmul_add, map_add, Finset.sum_add_distrib]

theorem tComp_smul_left (d : SupercategoryData) {X Y Z : d.Obj}
    (r : ℝ) (f : THom d X Y) (g : THom d Y Z) :
    tComp d (r • f) g = r • tComp d f g := by
  funext a
  simp [tComp, ← TensorProduct.smul_tmul', map_smul, Finset.smul_sum]

theorem tComp_smul_right (d : SupercategoryData) {X Y Z : d.Obj}
    (r : ℝ) (f : THom d X Y) (g : THom d Y Z) :
    tComp d f (r • g) = r • tComp d f g := by
  funext a
  simp [tComp, TensorProduct.tmul_smul, map_smul, Finset.smul_sum]

theorem tComp_even_left (d : SupercategoryData) {X Y Z : d.Obj}
    (f : EHom d X Y) (g : THom d Y Z) (a : ZMod 2) :
    tComp d (evenPoint f) g a = d.comp X Y Z a
      (ιTensorObj (d.Hom X Y) (d.Hom Y Z) 0 a a (zero_add a)
        (evenPoint f 0 ⊗ₜ[ℝ] g a)) := by
  classical
  unfold tComp
  rw [Finset.sum_eq_single 0]
  · rcases Classification.parity_cases a with rfl | rfl <;> rfl
  · intro b _ hb
    simp [evenPoint, homogeneousPoint, hb]
  · simp

theorem enriched_id_comp_at (C : Supercategory) (X Y : C.data.Obj)
    (a : ZMod 2) (f : C.data.Hom X Y a) :
    C.data.comp X X Y a
      (ιTensorObj (C.data.Hom X X) (C.data.Hom X Y) 0 a a (zero_add a)
        (evenPoint (C.data.id X) 0 ⊗ₜ[ℝ] f)) = f := by
  have h := congrFun (C.laws.id_comp X Y) a
  change (GradedObject.Monoidal.leftUnitor (C.data.Hom X Y)).inv a ≫
    GradedObject.Monoidal.tensorHom (C.data.id X) (𝟙 (C.data.Hom X Y)) a ≫
    C.data.comp X X Y a = 𝟙 (C.data.Hom X Y a) at h
  erw [GradedObject.Monoidal.leftUnitor_inv_apply, assoc, assoc,
    ι_tensorHom_assoc] at h
  have hf := congrArg (fun q => q f) h
  have hid : (𝟙 (C.data.Hom X Y)) a = 𝟙 (C.data.Hom X Y a) := rfl
  rw [hid] at hf
  simp only [ModuleCat.comp_apply, ModuleCat.id_apply,
    ModuleCat.MonoidalCategory.leftUnitor_inv_apply,
    ModuleCat.MonoidalCategory.whiskerRight_apply, ModuleCat.MonoidalCategory.tensorHom_tmul,
    tensorUnit₀] at hf
  convert! hf

theorem tComp_id_left (C : Supercategory) {X Y : C.data.Obj} (f : THom C.data X Y) :
    tComp C.data (evenPoint (C.data.id X)) f = f := by
  funext a
  rw [tComp_even_left, enriched_id_comp_at]

theorem tComp_even_right (d : SupercategoryData) {X Y Z : d.Obj}
    (f : THom d X Y) (g : EHom d Y Z) (a : ZMod 2) :
    tComp d f (evenPoint g) a = d.comp X Y Z a
      (ιTensorObj (d.Hom X Y) (d.Hom Y Z) a 0 a (add_zero a)
        (f a ⊗ₜ[ℝ] evenPoint g 0)) := by
  classical
  unfold tComp
  rw [Finset.sum_eq_single a]
  · rcases Classification.parity_cases a with rfl | rfl <;> rfl
  · intro b _ hb
    have hab : a - b ≠ 0 := sub_ne_zero.mpr (Ne.symm hb)
    simp [evenPoint, homogeneousPoint, hab]
  · simp

theorem enriched_comp_id_at (C : Supercategory) (X Y : C.data.Obj)
    (a : ZMod 2) (f : C.data.Hom X Y a) :
    C.data.comp X Y Y a
      (ιTensorObj (C.data.Hom X Y) (C.data.Hom Y Y) a 0 a (add_zero a)
        (f ⊗ₜ[ℝ] evenPoint (C.data.id Y) 0)) = f := by
  have h := congrFun (C.laws.comp_id X Y) a
  change (GradedObject.Monoidal.rightUnitor (C.data.Hom X Y)).inv a ≫
    GradedObject.Monoidal.tensorHom (𝟙 (C.data.Hom X Y)) (C.data.id Y) a ≫
    C.data.comp X Y Y a = 𝟙 (C.data.Hom X Y a) at h
  erw [GradedObject.Monoidal.rightUnitor_inv_apply, assoc, assoc,
    ι_tensorHom_assoc] at h
  have hf := congrArg (fun q => q f) h
  have hid : (𝟙 (C.data.Hom X Y)) a = 𝟙 (C.data.Hom X Y a) := rfl
  rw [hid] at hf
  simp only [ModuleCat.comp_apply, ModuleCat.id_apply,
    ModuleCat.MonoidalCategory.rightUnitor_inv_apply,
    ModuleCat.MonoidalCategory.whiskerLeft_apply, ModuleCat.MonoidalCategory.tensorHom_tmul,
    tensorUnit₀] at hf
  convert! hf

theorem tComp_id_right (C : Supercategory) {X Y : C.data.Obj} (f : THom C.data X Y) :
    tComp C.data f (evenPoint (C.data.id Y)) = f := by
  funext a
  rw [tComp_even_right, enriched_comp_id_at]

def componentComp (d : SupercategoryData) {X Y Z : d.Obj} (i j a : ZMod 2)
    (h : i + j = a) (f : d.Hom X Y i) (g : d.Hom Y Z j) : d.Hom X Z a :=
  d.comp X Y Z a (ιTensorObj (d.Hom X Y) (d.Hom Y Z) i j a h (f ⊗ₜ[ℝ] g))

theorem componentComp_assoc (C : Supercategory) (W X Y Z : C.data.Obj)
    (i j k a : ZMod 2) (h : i + j + k = a)
    (f : C.data.Hom W X i) (g : C.data.Hom X Y j) (q : C.data.Hom Y Z k) :
    componentComp C.data (i + j) k a h (componentComp C.data i j (i + j) rfl f g) q =
      componentComp C.data i (j + k) a (by rw [← add_assoc, h]) f
        (componentComp C.data j k (j + k) rfl g q) := by
  let A := C.data.Hom W X
  let B := C.data.Hom X Y
  let D := C.data.Hom Y Z
  have hc := congrArg (fun t => ιTensorObj₃ A B D i j k a h ≫ t a) (C.laws.assoc W X Y Z)
  change ιTensorObj₃ A B D i j k a h ≫
      ((GradedObject.Monoidal.associator A B D).inv a ≫
        GradedObject.Monoidal.tensorHom (C.data.comp W X Y) (𝟙 D) a ≫ C.data.comp W Y Z a) =
    ιTensorObj₃ A B D i j k a h ≫
      (GradedObject.Monoidal.tensorHom (𝟙 A) (C.data.comp X Y Z) a ≫ C.data.comp W X Z a) at hc
  erw [ιTensorObj₃_associator_inv_assoc,
    ιTensorObj₃'_eq A B D i j k a h _ rfl, assoc, assoc, ι_tensorHom_assoc,
    ι_tensorHom_assoc] at hc
  have he := congrArg (fun t => t (f ⊗ₜ[ℝ] (g ⊗ₜ[ℝ] q))) hc
  simp only [ModuleCat.comp_apply, ModuleCat.MonoidalCategory.associator_inv_apply,
    ModuleCat.MonoidalCategory.whiskerLeft_apply,
    ModuleCat.MonoidalCategory.tensorHom_tmul] at he
  convert! he

@[simp]
theorem componentComp_add_left (d : SupercategoryData) {X Y Z : d.Obj}
    (i j a : ZMod 2) (h : i + j = a) (f g : d.Hom X Y i) (q : d.Hom Y Z j) :
    componentComp d i j a h (f + g) q =
      componentComp d i j a h f q + componentComp d i j a h g q := by
  simp [componentComp, TensorProduct.add_tmul]

@[simp]
theorem componentComp_add_right (d : SupercategoryData) {X Y Z : d.Obj}
    (i j a : ZMod 2) (h : i + j = a) (f : d.Hom X Y i) (g q : d.Hom Y Z j) :
    componentComp d i j a h f (g + q) =
      componentComp d i j a h f g + componentComp d i j a h f q := by
  simp [componentComp, TensorProduct.tmul_add]

theorem tComp_zero (d : SupercategoryData) {X Y Z : d.Obj}
    (f : THom d X Y) (g : THom d Y Z) :
    tComp d f g 0 = componentComp d 0 0 0 rfl (f 0) (g 0) +
      componentComp d 1 1 0 rfl (f 1) (g 1) := by
  unfold tComp
  erw [Fin.sum_univ_two]
  rfl

theorem tComp_one (d : SupercategoryData) {X Y Z : d.Obj}
    (f : THom d X Y) (g : THom d Y Z) :
    tComp d f g 1 = componentComp d 0 1 1 rfl (f 0) (g 1) +
      componentComp d 1 0 1 rfl (f 1) (g 0) := by
  unfold tComp
  erw [Fin.sum_univ_two]
  rfl

/-- Associativity of total composition is the sum of homogeneous associativity. -/
theorem tComp_assoc (C : Supercategory) {W X Y Z : C.data.Obj}
    (f : THom C.data W X) (g : THom C.data X Y) (q : THom C.data Y Z) :
    tComp C.data (tComp C.data f g) q = tComp C.data f (tComp C.data g q) := by
  have h (i j k : ZMod 2) := componentComp_assoc C W X Y Z i j k (i + j + k)
    rfl (f i) (g j) (q k)
  funext a
  rcases Classification.parity_cases a with rfl | rfl <;>
    simp only [tComp_zero, tComp_one, componentComp_add_left, componentComp_add_right]
  · erw [h 0 0 0, h 1 1 0, h 0 1 1, h 1 0 1]
    ac_rfl
  · erw [h 0 0 1, h 1 1 1, h 0 1 0, h 1 0 0]
    ac_rfl

end RMod.Legacy
