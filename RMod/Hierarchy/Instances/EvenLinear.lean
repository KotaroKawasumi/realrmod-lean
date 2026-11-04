import RMod.Hierarchy.Abstract.Supercategory

/-!
# Linear structure on the even category

Mathlib's underlying category has Hom objects represented by maps from the
tensor unit. Its additive and scalar operations are inherited from sVec.
-/

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.MonoidalCategory
namespace RMod.Legacy

instance evenCategoryPreadditive (C : Supercategory) : Preadditive (Even C) where
  homGroup X Y := inferInstanceAs (AddCommGroup (EHom C.data X Y))
  add_comp X Y Z f g h := by
    change EHom C.data X Y at f g
    change EHom C.data Y Z at h
    change (λ_ (𝟙_ SuperVec)).inv ≫ ((f + g) ⊗ₘ h) ≫ C.data.comp X Y Z =
      ((λ_ (𝟙_ SuperVec)).inv ≫ (f ⊗ₘ h) ≫ C.data.comp X Y Z) +
      ((λ_ (𝟙_ SuperVec)).inv ≫ (g ⊗ₘ h) ≫ C.data.comp X Y Z)
    rw [MonoidalPreadditive.add_tensor, Preadditive.add_comp, Preadditive.comp_add]
  comp_add X Y Z f g h := by
    change EHom C.data X Y at f
    change EHom C.data Y Z at g h
    change (λ_ (𝟙_ SuperVec)).inv ≫ (f ⊗ₘ (g + h)) ≫ C.data.comp X Y Z =
      ((λ_ (𝟙_ SuperVec)).inv ≫ (f ⊗ₘ g) ≫ C.data.comp X Y Z) +
      ((λ_ (𝟙_ SuperVec)).inv ≫ (f ⊗ₘ h) ≫ C.data.comp X Y Z)
    rw [MonoidalPreadditive.tensor_add, Preadditive.add_comp, Preadditive.comp_add]

instance evenCategoryLinear (C : Supercategory) : Linear ℝ (Even C) where
  homModule X Y := inferInstanceAs (Module ℝ (EHom C.data X Y))
  smul_comp X Y Z r f g := by
    change EHom C.data X Y at f
    change EHom C.data Y Z at g
    change (λ_ (𝟙_ SuperVec)).inv ≫ ((r • f) ⊗ₘ g) ≫ C.data.comp X Y Z =
      r • ((λ_ (𝟙_ SuperVec)).inv ≫ (f ⊗ₘ g) ≫ C.data.comp X Y Z)
    simp only [MonoidalCategory.tensorHom_def, MonoidalLinear.smul_whiskerRight,
      Linear.smul_comp, Linear.comp_smul]
  comp_smul X Y Z f r g := by
    change EHom C.data X Y at f
    change EHom C.data Y Z at g
    change (λ_ (𝟙_ SuperVec)).inv ≫ (f ⊗ₘ (r • g)) ≫ C.data.comp X Y Z =
      r • ((λ_ (𝟙_ SuperVec)).inv ≫ (f ⊗ₘ g) ≫ C.data.comp X Y Z)
    simp only [MonoidalCategory.tensorHom_def, MonoidalLinear.whiskerLeft_smul,
      Linear.smul_comp, Linear.comp_smul]

end RMod.Legacy
