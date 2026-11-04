import RMod.Hierarchy.Instances.Koszul
import RMod.Classification.Proofs.Parity
import Mathlib.Tactic.NormNum

/-! Naturality and coherence of the Koszul braiding. -/

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Category
open GradedObject.Monoidal
namespace RMod.Legacy

theorem koszul_naturality_left {X Y : SuperVec} (f : X ⟶ Y) (Z : SuperVec) :
    (f ▷ Z) ≫ koszulMap Y Z = koszulMap X Z ≫ (Z ◁ f) := by
  funext a
  apply tensorObj_ext
  intro i j h
  change ιTensorObj X Z i j a h ≫
    (GradedObject.Monoidal.tensorHom f (𝟙 Z) a ≫ koszulMap Y Z a) =
    ιTensorObj X Z i j a h ≫
      (koszulMap X Z a ≫ GradedObject.Monoidal.tensorHom (𝟙 Z) f a)
  erw [ι_tensorHom_assoc, ι_koszulMap,
    Linear.comp_smul, ι_koszulMap_assoc, Linear.smul_comp, assoc, ι_tensorHom]
  congr 1
  erw [← assoc, BraidedCategory.braiding_naturality, assoc]

theorem koszul_naturality_right (X : SuperVec) {Y Z : SuperVec} (f : Y ⟶ Z) :
    (X ◁ f) ≫ koszulMap X Z = koszulMap X Y ≫ (f ▷ X) := by
  funext a
  apply tensorObj_ext
  intro i j h
  change ιTensorObj X Y i j a h ≫
    (GradedObject.Monoidal.tensorHom (𝟙 X) f a ≫ koszulMap X Z a) =
    ιTensorObj X Y i j a h ≫
      (koszulMap X Y a ≫ GradedObject.Monoidal.tensorHom f (𝟙 X) a)
  erw [ι_tensorHom_assoc, ι_koszulMap,
    Linear.comp_smul, ι_koszulMap_assoc, Linear.smul_comp, assoc, ι_tensorHom]
  congr 1
  erw [← assoc, BraidedCategory.braiding_naturality, assoc]

theorem koszulSign_add_right (i j k : ZMod 2) :
    (-1 : ℝ) ^ (i * (j + k)).val =
      (-1 : ℝ) ^ (i * j).val * (-1 : ℝ) ^ (i * k).val := by
  rcases Classification.parity_cases i with rfl | rfl <;>
    rcases Classification.parity_cases j with rfl | rfl <;>
    rcases Classification.parity_cases k with rfl | rfl <;>
    norm_num [ZMod.val_ofNat, ZMod.val_one]

theorem koszulSign_add_left (i j k : ZMod 2) :
    (-1 : ℝ) ^ ((i + j) * k).val =
      (-1 : ℝ) ^ (i * k).val * (-1 : ℝ) ^ (j * k).val := by
  simpa only [mul_comm _ k] using koszulSign_add_right k i j

end RMod.Legacy
