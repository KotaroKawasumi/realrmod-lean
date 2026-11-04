import Mathlib

/-!
# Linear structure on real super vector spaces

The Hom groups and scalar actions are pointwise. The graded tensor product
is Mathlib's coproduct tensor product; its additivity and linearity follow
by restricting to each homogeneous tensor summand.
-/

noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 256
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Category
namespace RMod.Legacy

@[implicit_reducible] def SuperVec := GradedObject (ZMod 2) (ModuleCat.{0} ℝ)
instance moduleCatHasInitial : HasInitial (ModuleCat.{0} ℝ) := inferInstance
instance : Category SuperVec := inferInstanceAs (Category (GradedObject _ _))
instance : MonoidalCategory SuperVec := inferInstanceAs (MonoidalCategory (GradedObject _ _))

instance superVecPreadditive : Preadditive SuperVec where
  homGroup X Y := inferInstanceAs (AddCommGroup (∀ a, X a ⟶ Y a))
  add_comp _ _ _ f g h := funext fun a => Preadditive.add_comp _ _ _ (f a) (g a) (h a)
  comp_add _ _ _ f g h := funext fun a => Preadditive.comp_add _ _ _ (f a) (g a) (h a)

instance superVecLinear : Linear ℝ SuperVec where
  homModule X Y := inferInstanceAs (Module ℝ (∀ a, X a ⟶ Y a))
  smul_comp _ _ _ r f g := funext fun a => Linear.smul_comp _ _ _ r (f a) (g a)
  comp_smul _ _ _ f r g := funext fun a => Linear.comp_smul _ _ _ (f a) r (g a)

open GradedObject.Monoidal in
@[implicit_reducible, instance] def superVecMonoidalPreadditive : MonoidalPreadditive SuperVec where
  whiskerLeft_zero := by
    intro X Y Z
    funext a
    apply tensorObj_ext
    intro i j h
    change ιTensorObj X Y i j a h ≫ GradedObject.Monoidal.tensorHom (𝟙 X) 0 a = _
    rw [ι_tensorHom]
    change ((𝟙 (X i)) ⊗ₘ (0 : Y j ⟶ Z j)) ≫ _ = _ ≫ 0
    simp
  zero_whiskerRight := by
    intro X Y Z
    funext a
    apply tensorObj_ext
    intro i j h
    change ιTensorObj Y X i j a h ≫ GradedObject.Monoidal.tensorHom 0 (𝟙 X) a = _
    rw [ι_tensorHom]
    change ((0 : Y i ⟶ Z i) ⊗ₘ (𝟙 (X j))) ≫ _ = _ ≫ 0
    simp
  whiskerLeft_add := by
    intro X Y Z f g
    funext a
    apply tensorObj_ext
    intro i j h
    change ιTensorObj X Y i j a h ≫ GradedObject.Monoidal.tensorHom (𝟙 X) (f + g) a = _
    change ιTensorObj X Y i j a h ≫ GradedObject.Monoidal.tensorHom (𝟙 X) (f + g) a =
      ιTensorObj X Y i j a h ≫
        (GradedObject.Monoidal.tensorHom (𝟙 X) f a + GradedObject.Monoidal.tensorHom (𝟙 X) g a)
    rw [Preadditive.comp_add, ι_tensorHom, ι_tensorHom, ι_tensorHom]
    change ((𝟙 (X i)) ⊗ₘ (f j + g j)) ≫ _ = _
    rw [MonoidalPreadditive.tensor_add, Preadditive.add_comp]
    rfl
  add_whiskerRight := by
    intro X Y Z f g
    funext a
    apply tensorObj_ext
    intro i j h
    change ιTensorObj Y X i j a h ≫ GradedObject.Monoidal.tensorHom (f + g) (𝟙 X) a = _
    change ιTensorObj Y X i j a h ≫ GradedObject.Monoidal.tensorHom (f + g) (𝟙 X) a =
      ιTensorObj Y X i j a h ≫
        (GradedObject.Monoidal.tensorHom f (𝟙 X) a + GradedObject.Monoidal.tensorHom g (𝟙 X) a)
    rw [Preadditive.comp_add, ι_tensorHom, ι_tensorHom, ι_tensorHom]
    change ((f i + g i) ⊗ₘ (𝟙 (X j))) ≫ _ = _
    rw [MonoidalPreadditive.add_tensor, Preadditive.add_comp]
    rfl

open GradedObject.Monoidal in
@[implicit_reducible, instance] def superVecMonoidalLinear : MonoidalLinear ℝ SuperVec where
  whiskerLeft_smul := by
    intro X Y Z r f
    funext a
    apply tensorObj_ext
    intro i j h
    change ιTensorObj X Y i j a h ≫ GradedObject.Monoidal.tensorHom (𝟙 X) (r • f) a = _
    change ιTensorObj X Y i j a h ≫ GradedObject.Monoidal.tensorHom (𝟙 X) (r • f) a =
      ιTensorObj X Y i j a h ≫ (r • GradedObject.Monoidal.tensorHom (𝟙 X) f a)
    rw [Linear.comp_smul, ι_tensorHom, ι_tensorHom]
    change ((𝟙 (X i)) ⊗ₘ (r • f j)) ≫ _ = _
    simp only [MonoidalCategory.tensorHom_def, MonoidalLinear.whiskerLeft_smul,
      Linear.comp_smul, Linear.smul_comp]
    rfl
  smul_whiskerRight := by
    intro r Y Z f X
    funext a
    apply tensorObj_ext
    intro i j h
    change ιTensorObj Y X i j a h ≫ GradedObject.Monoidal.tensorHom (r • f) (𝟙 X) a = _
    change ιTensorObj Y X i j a h ≫ GradedObject.Monoidal.tensorHom (r • f) (𝟙 X) a =
      ιTensorObj Y X i j a h ≫ (r • GradedObject.Monoidal.tensorHom f (𝟙 X) a)
    rw [Linear.comp_smul, ι_tensorHom, ι_tensorHom]
    change ((r • f i) ⊗ₘ (𝟙 (X j))) ≫ _ = _
    simp only [MonoidalCategory.tensorHom_def, MonoidalLinear.smul_whiskerRight,
      Linear.smul_comp]
    rfl

end RMod.Legacy
