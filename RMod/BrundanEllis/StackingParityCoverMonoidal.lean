import RMod.BrundanEllis.StackingParityCoverCategory

/-! Ordinary monoidal laws for the parity cover. The only new calculation
is the cancellation of the source-parity scalar against super-interchange.
All associators, unitors and their coherence are inherited unchanged. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v
namespace RMod.BrundanEllis.Stacking.ParityCover
open RMod.Classification CategoryTheory CategoryTheory.MonoidalCategory
variable (C : WeaklyPointedSuperfusion.{u, v})

@[simp] theorem id_val (X : ParityCover C) : (𝟙 X : X ⟶ X).val = C.data.id X.1 := rfl
@[simp] theorem comp_val {X Y Z : ParityCover C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).val = C.data.comp f.val g.val := rfl
@[simp] theorem tensorObj_fst (X Y : ParityCover C) : (X ⊗ Y).1 = C.data.tensorObj X.1 Y.1 := rfl
@[simp] theorem tensorObj_snd (X Y : ParityCover C) : (X ⊗ Y).2 = X.2 + Y.2 := rfl
@[simp] theorem tensor_val {X X' Y Y' : ParityCover C} (f : X ⟶ X') (g : Y ⟶ Y') :
    (f ⊗ₘ g).val = C.data.smul ((-1 : ℝ) ^ (X.2 * (Y.2 + Y'.2)).val)
      (C.data.tensorHom f.val g.val) := rfl
@[simp] theorem assoc_hom_val (X Y Z : ParityCover C) :
    (α_ X Y Z).hom.val = C.data.associatorHom X.1 Y.1 Z.1 := rfl
@[simp] theorem assoc_inv_val (X Y Z : ParityCover C) :
    (α_ X Y Z).inv.val = C.data.associatorInv X.1 Y.1 Z.1 := rfl
@[simp] theorem leftUnit_hom_val (X : ParityCover C) :
    (λ_ X).hom.val = C.data.leftUnitorHom X.1 := rfl
@[simp] theorem rightUnit_hom_val (X : ParityCover C) :
    (ρ_ X).hom.val = C.data.rightUnitorHom X.1 := rfl
@[simp] theorem unit_fst : (𝟙_ (ParityCover C)).1 = C.data.tensorUnit := rfl
@[simp] theorem unit_snd : (𝟙_ (ParityCover C)).2 = 0 := rfl

/-- This scalar identity is precisely the correction to super-interchange. -/
theorem tensor_scalar_comp (p p' q q' q'' : ZMod 2) :
    (-1 : ℝ) ^ (p * (q + q')).val *
      ((-1 : ℝ) ^ (p' * (q' + q'')).val * (-1 : ℝ) ^ ((q' + q'') * (p + p')).val) =
      (-1 : ℝ) ^ (p * (q + q'')).val := by
  simp only [← parity_power_add]
  congr 2
  ring_nf
  simp [CharTwo.two_eq_zero]

/-- The signed tensor is functorial on the actual homogeneous morphisms. -/
theorem tensor_comp {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : ParityCover C}
    (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂) :
    (f₁ ⊗ₘ f₂) ≫ (g₁ ⊗ₘ g₂) = (f₁ ≫ g₁) ⊗ₘ (f₂ ≫ g₂) := by
  apply Subtype.ext
  simp only [comp_val, tensor_val]
  rw [C.laws.smul_comp, C.laws.comp_smul,
    C.laws.super_interchange g₁.val g₂.val f₁.val f₂.val g₂.property f₁.property,
    ← C.laws.mul_smul, ← C.laws.mul_smul, mul_assoc, tensor_scalar_comp]

/-- The tensor identity map carries no correction. -/
theorem tensor_id (X Y : ParityCover C) : (𝟙 X) ⊗ₘ (𝟙 Y) = 𝟙 (X ⊗ Y) := by
  apply Subtype.ext
  simp only [tensor_val, id_val, tensorObj_fst, CharTwo.add_self_eq_zero, mul_zero,
    ZMod.val_zero, pow_zero, C.laws.one_smul, C.laws.tensor_id]

/-- The two scalar factors in associator naturality agree by distributivity. -/
theorem associator_natural {X₁ X₂ X₃ Y₁ Y₂ Y₃ : ParityCover C}
    (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃) :
    ((f₁ ⊗ₘ f₂) ⊗ₘ f₃) ≫ (α_ Y₁ Y₂ Y₃).hom =
      (α_ X₁ X₂ X₃).hom ≫ (f₁ ⊗ₘ (f₂ ⊗ₘ f₃)) := by
  apply Subtype.ext
  simp only [comp_val, tensor_val, tensorObj_snd, assoc_hom_val]
  rw [C.laws.tensor_smul_left, C.laws.tensor_smul_right,
    C.laws.smul_comp, C.laws.smul_comp, C.laws.comp_smul, C.laws.comp_smul,
    C.laws.associator_naturality, ← C.laws.mul_smul, ← C.laws.mul_smul]
  congr 1
  simp only [← parity_power_add]
  congr 2
  ring

instance monoidal : MonoidalCategory (ParityCover C) :=
  MonoidalCategory.ofTensorHom
    (id_tensorHom_id := tensor_id C)
    (id_tensorHom := fun X {Y Y'} f => rfl)
    (tensorHom_id := fun {X X'} f Y => rfl)
    (tensorHom_comp_tensorHom := tensor_comp C)
    (associator_naturality := associator_natural C)
    (leftUnitor_naturality := by
      intro X Y f
      apply Subtype.ext
      simp only [comp_val, tensor_val, unit_snd, zero_mul, ZMod.val_zero, pow_zero,
        C.laws.one_smul, id_val, unit_fst, leftUnit_hom_val]
      exact C.laws.left_unitor_naturality f.val)
    (rightUnitor_naturality := by
      intro X Y f
      apply Subtype.ext
      simp only [comp_val, tensor_val, unit_snd, add_zero, mul_zero, ZMod.val_zero, pow_zero,
        C.laws.one_smul, id_val, unit_fst, rightUnit_hom_val]
      exact C.laws.right_unitor_naturality f.val)
    (pentagon := by
      intro W X Y Z
      apply Subtype.ext
      simp only [comp_val, tensor_val, tensorObj_snd, tensorObj_fst, id_val, assoc_hom_val,
        add_assoc, CharTwo.add_self_eq_zero, mul_zero, ZMod.val_zero, pow_zero, C.laws.one_smul]
      exact (C.laws.comp_assoc _ _ _).symm.trans (C.laws.pentagon W.1 X.1 Y.1 Z.1))
    (triangle := by
      intro X Y
      apply Subtype.ext
      simp only [comp_val, tensor_val, tensorObj_snd, tensorObj_fst, unit_snd, unit_fst,
        id_val, assoc_hom_val, leftUnit_hom_val, rightUnit_hom_val, zero_add,
        CharTwo.add_self_eq_zero, mul_zero, ZMod.val_zero, pow_zero, C.laws.one_smul]
      exact C.laws.triangle X.1 Y.1)

end RMod.BrundanEllis.Stacking.ParityCover
