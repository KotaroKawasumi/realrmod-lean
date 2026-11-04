import RMod.Enriched.SuperBasics
import RMod.Classification.Proofs.Parity

/-! Associativity, identities, and linearity of the two-component convolution. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Category
open GradedObject.Monoidal
open scoped BigOperators TensorProduct
universe u
namespace RMod.EnrichedSupport

abbrev EHom (C : Type u) [SuperCategory C] (X Y : C) := 𝟙_ SuperVec ⟶ SHom C X Y

theorem tComp_add_left (d : Type u) [SuperCategory d] {X Y Z : d}
    (f g : THom d X Y) (h : THom d Y Z) :
    tComp d (f + g) h = tComp d f h + tComp d g h := by
  funext a
  simp [tComp, TensorProduct.add_tmul, map_add, Finset.sum_add_distrib]

theorem tComp_add_right (d : Type u) [SuperCategory d] {X Y Z : d}
    (f : THom d X Y) (g h : THom d Y Z) :
    tComp d f (g + h) = tComp d f g + tComp d f h := by
  funext a
  simp [tComp, TensorProduct.tmul_add, map_add, Finset.sum_add_distrib]

theorem tComp_smul_left (d : Type u) [SuperCategory d] {X Y Z : d}
    (r : ℝ) (f : THom d X Y) (g : THom d Y Z) :
    tComp d (r • f) g = r • tComp d f g := by
  funext a
  simp [tComp, ← TensorProduct.smul_tmul', map_smul, Finset.smul_sum]

theorem tComp_smul_right (d : Type u) [SuperCategory d] {X Y Z : d}
    (r : ℝ) (f : THom d X Y) (g : THom d Y Z) :
    tComp d f (r • g) = r • tComp d f g := by
  funext a
  simp [tComp, TensorProduct.tmul_smul, map_smul, Finset.smul_sum]

theorem tComp_even_left (d : Type u) [SuperCategory d] {X Y Z : d}
    (f : EHom d X Y) (g : THom d Y Z) (a : ZMod 2) :
    tComp d (evenPoint f) g a = eComp SuperVec X Y Z a
      (ιTensorObj (SHom d X Y) (SHom d Y Z) 0 a a (zero_add a)
        (evenPoint f 0 ⊗ₜ[ℝ] g a)) := by
  classical
  unfold tComp
  rw [Finset.sum_eq_single 0]
  · rcases Classification.parity_cases a with rfl | rfl <;> rfl
  · intro b _ hb
    simp [evenPoint, homogeneousPoint, hb]
  · simp

theorem enriched_id_comp_at (C : Type u) [SuperCategory C] (X Y : C)
    (a : ZMod 2) (f : SHom C X Y a) :
    eComp SuperVec X X Y a
      (ιTensorObj (SHom C X X) (SHom C X Y) 0 a a (zero_add a)
        (evenPoint (eId SuperVec X) 0 ⊗ₜ[ℝ] f)) = f := by
  have h := congrFun (e_id_comp SuperVec X Y) a
  change (GradedObject.Monoidal.leftUnitor (SHom C X Y)).inv a ≫
    GradedObject.Monoidal.tensorHom (eId SuperVec X) (𝟙 (SHom C X Y)) a ≫
    eComp SuperVec X X Y a = 𝟙 (SHom C X Y a) at h
  erw [GradedObject.Monoidal.leftUnitor_inv_apply, assoc, assoc,
    ι_tensorHom_assoc] at h
  have hf := congrArg (fun q => q f) h
  have hid : (𝟙 (SHom C X Y)) a = 𝟙 (SHom C X Y a) := rfl
  rw [hid] at hf
  simp only [ModuleCat.comp_apply, ModuleCat.id_apply,
    ModuleCat.MonoidalCategory.leftUnitor_inv_apply,
    ModuleCat.MonoidalCategory.whiskerRight_apply, ModuleCat.MonoidalCategory.tensorHom_tmul,
    tensorUnit₀] at hf
  convert! hf

theorem tComp_id_left (C : Type u) [SuperCategory C] {X Y : C} (f : THom C X Y) :
    tComp C (evenPoint (eId SuperVec X)) f = f := by
  funext a
  rw [tComp_even_left, enriched_id_comp_at]

theorem tComp_even_right (d : Type u) [SuperCategory d] {X Y Z : d}
    (f : THom d X Y) (g : EHom d Y Z) (a : ZMod 2) :
    tComp d f (evenPoint g) a = eComp SuperVec X Y Z a
      (ιTensorObj (SHom d X Y) (SHom d Y Z) a 0 a (add_zero a)
        (f a ⊗ₜ[ℝ] evenPoint g 0)) := by
  classical
  unfold tComp
  rw [Finset.sum_eq_single a]
  · rcases Classification.parity_cases a with rfl | rfl <;> rfl
  · intro b _ hb
    have hab : a - b ≠ 0 := sub_ne_zero.mpr (Ne.symm hb)
    simp [evenPoint, homogeneousPoint, hab]
  · simp

theorem enriched_comp_id_at (C : Type u) [SuperCategory C] (X Y : C)
    (a : ZMod 2) (f : SHom C X Y a) :
    eComp SuperVec X Y Y a
      (ιTensorObj (SHom C X Y) (SHom C Y Y) a 0 a (add_zero a)
        (f ⊗ₜ[ℝ] evenPoint (eId SuperVec Y) 0)) = f := by
  have h := congrFun (e_comp_id SuperVec X Y) a
  change (GradedObject.Monoidal.rightUnitor (SHom C X Y)).inv a ≫
    GradedObject.Monoidal.tensorHom (𝟙 (SHom C X Y)) (eId SuperVec Y) a ≫
    eComp SuperVec X Y Y a = 𝟙 (SHom C X Y a) at h
  erw [GradedObject.Monoidal.rightUnitor_inv_apply, assoc, assoc,
    ι_tensorHom_assoc] at h
  have hf := congrArg (fun q => q f) h
  have hid : (𝟙 (SHom C X Y)) a = 𝟙 (SHom C X Y a) := rfl
  rw [hid] at hf
  simp only [ModuleCat.comp_apply, ModuleCat.id_apply,
    ModuleCat.MonoidalCategory.rightUnitor_inv_apply,
    ModuleCat.MonoidalCategory.whiskerLeft_apply, ModuleCat.MonoidalCategory.tensorHom_tmul,
    tensorUnit₀] at hf
  convert! hf

theorem tComp_id_right (C : Type u) [SuperCategory C] {X Y : C} (f : THom C X Y) :
    tComp C f (evenPoint (eId SuperVec Y)) = f := by
  funext a
  rw [tComp_even_right, enriched_comp_id_at]

def componentComp (d : Type u) [SuperCategory d] {X Y Z : d} (i j a : ZMod 2)
    (h : i + j = a) (f : SHom d X Y i) (g : SHom d Y Z j) : SHom d X Z a :=
  eComp SuperVec X Y Z a (ιTensorObj (SHom d X Y) (SHom d Y Z) i j a h (f ⊗ₜ[ℝ] g))

theorem componentComp_assoc (C : Type u) [SuperCategory C] (W X Y Z : C)
    (i j k a : ZMod 2) (h : i + j + k = a)
    (f : SHom C W X i) (g : SHom C X Y j) (q : SHom C Y Z k) :
    componentComp C (i + j) k a h (componentComp C i j (i + j) rfl f g) q =
      componentComp C i (j + k) a (by rw [← add_assoc, h]) f
        (componentComp C j k (j + k) rfl g q) := by
  let A := SHom C W X
  let B := SHom C X Y
  let D := SHom C Y Z
  have hc := congrArg (fun t => ιTensorObj₃ A B D i j k a h ≫ t a) (e_assoc SuperVec W X Y Z)
  change ιTensorObj₃ A B D i j k a h ≫
      ((GradedObject.Monoidal.associator A B D).inv a ≫
        GradedObject.Monoidal.tensorHom (eComp SuperVec W X Y) (𝟙 D) a ≫ eComp SuperVec W Y Z a) =
    ιTensorObj₃ A B D i j k a h ≫
      (GradedObject.Monoidal.tensorHom (𝟙 A) (eComp SuperVec X Y Z) a ≫ eComp SuperVec W X Z a) at hc
  erw [ιTensorObj₃_associator_inv_assoc,
    ιTensorObj₃'_eq A B D i j k a h _ rfl, assoc, assoc, ι_tensorHom_assoc,
    ι_tensorHom_assoc] at hc
  have he := congrArg (fun t => t (f ⊗ₜ[ℝ] (g ⊗ₜ[ℝ] q))) hc
  simp only [ModuleCat.comp_apply, ModuleCat.MonoidalCategory.associator_inv_apply,
    ModuleCat.MonoidalCategory.whiskerLeft_apply,
    ModuleCat.MonoidalCategory.tensorHom_tmul] at he
  convert! he

@[simp]
theorem componentComp_add_left (d : Type u) [SuperCategory d] {X Y Z : d}
    (i j a : ZMod 2) (h : i + j = a) (f g : SHom d X Y i) (q : SHom d Y Z j) :
    componentComp d i j a h (f + g) q =
      componentComp d i j a h f q + componentComp d i j a h g q := by
  simp [componentComp, TensorProduct.add_tmul]

@[simp]
theorem componentComp_add_right (d : Type u) [SuperCategory d] {X Y Z : d}
    (i j a : ZMod 2) (h : i + j = a) (f : SHom d X Y i) (g q : SHom d Y Z j) :
    componentComp d i j a h f (g + q) =
      componentComp d i j a h f g + componentComp d i j a h f q := by
  simp [componentComp, TensorProduct.tmul_add]

theorem tComp_zero (d : Type u) [SuperCategory d] {X Y Z : d}
    (f : THom d X Y) (g : THom d Y Z) :
    tComp d f g 0 = componentComp d 0 0 0 rfl (f 0) (g 0) +
      componentComp d 1 1 0 rfl (f 1) (g 1) := by
  unfold tComp
  erw [Fin.sum_univ_two]
  rfl

theorem tComp_one (d : Type u) [SuperCategory d] {X Y Z : d}
    (f : THom d X Y) (g : THom d Y Z) :
    tComp d f g 1 = componentComp d 0 1 1 rfl (f 0) (g 1) +
      componentComp d 1 0 1 rfl (f 1) (g 0) := by
  unfold tComp
  erw [Fin.sum_univ_two]
  rfl

/-- Associativity of total composition is the sum of homogeneous associativity. -/
theorem tComp_assoc (C : Type u) [SuperCategory C] {W X Y Z : C}
    (f : THom C W X) (g : THom C X Y) (q : THom C Y Z) :
    tComp C (tComp C f g) q = tComp C f (tComp C g q) := by
  have h (i j k : ZMod 2) := componentComp_assoc C W X Y Z i j k (i + j + k)
    rfl (f i) (g j) (q k)
  funext a
  rcases Classification.parity_cases a with rfl | rfl <;>
    simp only [tComp_zero, tComp_one, componentComp_add_left, componentComp_add_right]
  · erw [h 0 0 0, h 1 1 0, h 0 1 1, h 1 0 1]
    ac_rfl
  · erw [h 0 0 1, h 1 1 1, h 0 1 0, h 1 0 0]
    ac_rfl

end RMod.EnrichedSupport
